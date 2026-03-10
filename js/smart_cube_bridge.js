"use strict";

/**
 * SmartCubeBridge - csTimerのスマートキューブBluetooth通信ファイルを
 * 他のタイマーアプリで利用するためのブリッジモジュール
 *
 * 使い方:
 *   1. このファイルを最初に読み込む
 *   2. csTimerの元ファイルを順番に読み込む
 *   3. SmartCubeBridge.onMove() でコールバックを登録
 *   4. SmartCubeBridge.connect() で接続開始
 *
 * 読み込み順序:
 *   smart_cube_bridge.js  (このファイル)
 *   cstimer/mathlib.js
 *   cstimer/sha256.js
 *   cstimer/lzstring.js
 *   cstimer/bluetooth.js
 *   cstimer/giikercube.js
 *   cstimer/gancube.js
 *   cstimer/gocube.js
 *   cstimer/moyucube.js
 *   cstimer/moyu32cube.js
 *   cstimer/qiyicube.js
 */

// =============================================================================
// グローバル変数の補完 (csTimer元ファイルが参照するスタブ)
// =============================================================================

// --- execMain / execBoth / execWorker ---
// csTimerのモジュールシステム。メインスレッドで関数を即実行する。
var isInNode = false;
var isInWorker = false;
var ISCSTIMER = false; // csTimer固有の初期化をスキップ
var DEBUGM = false;
var DEBUGWK = false;
var DEBUG = false;
var DEBUGBL = false;

function execBoth(funcMain, funcWorker, params) {
    if (!isInWorker && funcMain) {
        return funcMain.apply(this, params || []);
    }
    return {};
}

function execWorker(func, params) {
    return execBoth(undefined, func, params);
}

function execMain(func, params) {
    return execBoth(func, undefined, params);
}

// --- jQuery互換スタブ ($) ---
// csTimerの元ファイルが使用するjQueryメソッドの最小互換
if (typeof $ === 'undefined') {
    var $ = function () {
        // DOM関連は何もしない空オブジェクトを返す
        var noop = function () { return fakeJq; };
        var fakeJq = {
            css: noop, empty: noop, append: noop, html: noop,
            hide: noop, show: noop, unbind: noop, click: noop,
            width: noop, height: noop, attr: noop, val: noop,
            addClass: noop, appendTo: noop, focus: noop, select: noop,
            remove: noop, on: noop, off: noop, reclk: noop
        };
        return fakeJq;
    };
    $.isArray = Array.isArray;
    $.noop = function () { };
    $.now = function () {
        if (window.performance && window.performance.now) {
            return Math.floor(window.performance.now());
        }
        return +new Date;
    };
    $.map = function (arr, fn) {
        return Array.prototype.map.call(arr, fn);
    };
    $.delayExec = (function () {
        var tids = {};
        return function (key, func, timeout) {
            if (tids[key]) {
                clearTimeout(tids[key]);
                delete tids[key];
            }
            tids[key] = setTimeout(func, timeout);
        };
    })();
    $.format = function (format, args) {
        return format.replace(/{(\d+)}/g, function (m, num) { return args[~~num] || ''; });
    };
}

// --- 文字列定数 (csTimerの言語ファイルで定義されるもの) ---
var CONFIRM_GIIRST = 'Cube state is out of sync. Reset to solved state?';
var GIIKER_NOBLEMSG = 'Web Bluetooth is not available. Please use Chrome and enable Web Bluetooth.';
var GIIKER_CONNECT = 'Connect Smart Cube';
var GIIKER_RESET = 'Reset';
var GIIKER_REQMACMSG = 'Please enter the MAC address of the cube (format xx:xx:xx:xx:xx:xx):';
var LGHINT_BTNOTSUP = 'Bluetooth not supported';
var LGHINT_BTDISCON = 'Bluetooth disconnected';
var LGHINT_BTCONSUC = 'Bluetooth connected';
var LGHINT_BTINVMAC = 'Invalid MAC address';
var TOOLS_GIIKER = 'Smart Cube';

// --- logohint スタブ ---
var logohint = {
    push: function (msg) {
        SmartCubeBridge._log('[logohint]', msg);
    }
};

// --- kernel スタブ (設定の読み書き) ---
var kernel = (function () {
    var prefix = 'smartcube_';
    return {
        getProp: function (key, defaultVal) {
            try {
                var val = localStorage.getItem(prefix + key);
                return val !== null ? val : (defaultVal !== undefined ? defaultVal : '');
            } catch (e) {
                return defaultVal !== undefined ? defaultVal : '';
            }
        },
        setProp: function (key, val) {
            try {
                localStorage.setItem(prefix + key, val);
            } catch (e) { }
        },
        pushSignal: function () { },
        regListener: function () { },
        showDialog: function () { }
    };
})();

// --- scramble_333 スタブ ---
var scramble_333 = {
    genFacelet: function () { return ''; }
};

// --- tools / timer / cubeutil スタブ ---
var tools = {
    getCurPuzzle: function () { return '333'; },
    puzzleType: function () { return '333'; },
    regTool: function () { }
};

var timer = {
    getCurTime: function () { return 0; },
    status: function () { return 0; },
    getStartTime: function () { return 0; }
};

var cubeutil = {
    getConjMoves: function (s) { return s || ''; },
    parseScramble: function () { return []; },
    getProgress: function () { return 0; },
    moveSeq2str: function () { return ''; },
    getPreConj: function () { return 0; }
};

// --- CSTIMER_VERSION ---
var CSTIMER_VERSION = 'bridge';

// =============================================================================
// SmartCubeBridge - メインAPI
// =============================================================================

var SmartCubeBridge = (function () {
    var _moveCallbacks = [];
    var _connectCallbacks = [];
    var _disconnectCallbacks = [];
    var _stateCallbacks = [];
    var _debugEnabled = false;
    var _currentState = null;
    var _deviceName = null;

    function _log() {
        if (_debugEnabled) {
            console.log.apply(console, ['[SmartCubeBridge]'].concat(Array.from(arguments)));
        }
    }

    /**
     * GiikerCube.callbackを傍受して回転記号を通知する
     * csTimerの元ファイルが読み込まれた後に自動的にフックされる
     */
    function _hookCallback() {
        if (typeof GiikerCube === 'undefined') {
            _log('GiikerCube not loaded yet');
            return false;
        }

        GiikerCube.setCallback(function (facelet, prevMoves, lastTs, hardware) {
            _currentState = facelet;

            if (hardware && hardware !== _deviceName) {
                _deviceName = hardware;
            }

            // prevMoves[0] が最新の回転 (例: "U ", "R'", "F2")
            if (prevMoves && prevMoves.length > 0) {
                var rawMove = prevMoves[0]; // e.g. "U ", "R'", "F2"
                var moveStr = rawMove.replace(/\s+/g, ''); // トリミング

                // 注意: csTimerのドライバ層(gancube.js等)がmoveCntベースで
                // 重複チェックを行っているため、ブリッジ側での追加チェックは不要。
                // 以前のmoveStr+timestampベースの重複防止は、ロスト手番リカバリ時に
                // timestampがnullになる場合、同一面の連続回転(R R等)を誤って
                // フィルタしてしまう問題があった。

                var info = {
                    move: moveStr,
                    timestamp: lastTs ? lastTs[1] || lastTs[0] : Date.now(),
                    deviceTimestamp: lastTs ? lastTs[0] : null,
                    deviceName: hardware,
                    facelet: facelet,
                    prevMoves: prevMoves.map(function (m) { return m.replace(/\s+/g, ''); })
                };

                _log('Move:', moveStr, 'from', hardware);

                for (var i = 0; i < _moveCallbacks.length; i++) {
                    try {
                        _moveCallbacks[i](moveStr, info);
                    } catch (e) {
                        console.error('[SmartCubeBridge] Error in move callback:', e);
                    }
                }
            }

            // 状態変化の通知
            for (var i = 0; i < _stateCallbacks.length; i++) {
                try {
                    _stateCallbacks[i](facelet);
                } catch (e) {
                    console.error('[SmartCubeBridge] Error in state callback:', e);
                }
            }
        });

        GiikerCube.setEventCallback(function (info, event) {
            if (info === 'disconnect') {
                _log('Disconnected');
                _deviceName = null;
                for (var i = 0; i < _disconnectCallbacks.length; i++) {
                    try {
                        _disconnectCallbacks[i]();
                    } catch (e) {
                        console.error('[SmartCubeBridge] Error in disconnect callback:', e);
                    }
                }
            }
        });

        return true;
    }

    return {
        /**
         * 回転記号のコールバックを登録
         * @param {function(string, object)} callback - callback(move, info)
         *   move: "U", "U'", "U2", "R", "R'", "R2", etc.
         *   info: { move, timestamp, deviceName, facelet, prevMoves }
         */
        onMove: function (callback) {
            if (typeof callback === 'function') {
                _moveCallbacks.push(callback);
            }
        },

        /**
         * 接続完了時のコールバックを登録
         * @param {function(string)} callback - callback(deviceName)
         */
        onConnect: function (callback) {
            if (typeof callback === 'function') {
                _connectCallbacks.push(callback);
            }
        },

        /**
         * 切断時のコールバックを登録
         * @param {function()} callback
         */
        onDisconnect: function (callback) {
            if (typeof callback === 'function') {
                _disconnectCallbacks.push(callback);
            }
        },

        /**
         * キューブ状態変化時のコールバックを登録
         * @param {function(string)} callback - callback(facelet)
         */
        onStateChange: function (callback) {
            if (typeof callback === 'function') {
                _stateCallbacks.push(callback);
            }
        },

        /**
         * Bluetooth接続を開始
         * @returns {Promise}
         */
        connect: function () {
            if (typeof GiikerCube === 'undefined') {
                return Promise.reject('csTimer files not loaded. Check script loading order.');
            }

            _hookCallback();

            return GiikerCube.init().then(function () {
                _log('Connected');
                var name = '';
                try {
                    var cube = GiikerCube.getCube();
                    name = _deviceName || 'Smart Cube';
                } catch (e) { }
                for (var i = 0; i < _connectCallbacks.length; i++) {
                    try {
                        _connectCallbacks[i](name);
                    } catch (e) {
                        console.error('[SmartCubeBridge] Error in connect callback:', e);
                    }
                }
            });
        },

        /**
         * Bluetooth切断
         * @returns {Promise}
         */
        disconnect: function () {
            if (typeof GiikerCube === 'undefined' || !GiikerCube.isConnected()) {
                return Promise.resolve();
            }
            return GiikerCube.stop();
        },

        /**
         * 接続状態を確認
         * @returns {boolean}
         */
        isConnected: function () {
            return typeof GiikerCube !== 'undefined' && GiikerCube.isConnected();
        },

        /**
         * バッテリー残量を取得
         * @returns {Promise<number>} 0-100
         */
        getBatteryLevel: function () {
            if (typeof GiikerCube === 'undefined' || !GiikerCube.isConnected()) {
                return Promise.reject('Not connected');
            }
            var cube = GiikerCube.getCube();
            if (!cube || !cube.getBatteryLevel) {
                return Promise.reject('Battery level not supported');
            }
            return cube.getBatteryLevel().then(function (value) {
                // value is [level, deviceName]
                return Array.isArray(value) ? value[0] : value;
            });
        },

        /**
         * デバイス名を取得
         * @returns {string|null}
         */
        getDeviceName: function () {
            return _deviceName;
        },

        /**
         * 現在のキューブ状態 (facelet文字列) を取得
         * @returns {string|null} e.g. "UUUUUUUUURRRRRRRRRFFFFFFFFFDDDDDDDDDLLLLLLLLLBBBBBBBBB"
         */
        getCurrentState: function () {
            return _currentState;
        },

        /**
         * キューブ状態を解決済みとしてマーク
         */
        markSolved: function () {
            if (typeof giikerutil !== 'undefined' && giikerutil._bridge_markSolved) {
                giikerutil._bridge_markSolved();
            }
        },

        /**
         * デバッグログの有効/無効を切り替え
         * @param {boolean} enabled
         */
        setDebug: function (enabled) {
            _debugEnabled = !!enabled;
        },

        /**
         * 全コールバックをクリア
         */
        clearCallbacks: function () {
            _moveCallbacks = [];
            _connectCallbacks = [];
            _disconnectCallbacks = [];
            _stateCallbacks = [];
        },

        /** 内部ログ用 (他モジュールから参照) */
        _log: _log
    };
})();

// =============================================================================
// giikerutil スタブ (csTimerのbluetoothutil.jsの代替)
// =============================================================================

// giikerutilはbluetoothutil.jsで本来定義されるが、ブリッジでは最小限のスタブを提供
// bluetooth.jsの中でgiikerutil.chkAvail()とgiikerutil.log()が呼ばれる
var giikerutil = (function () {
    var _savedMacMap = {};
    try {
        _savedMacMap = JSON.parse(localStorage.getItem('smartcube_giiMacMap') || '{}');
    } catch (e) { }

    return {
        log: function () {
            SmartCubeBridge._log.apply(null, arguments);
        },
        chkAvail: function () {
            if (!window.navigator || !window.navigator.bluetooth) {
                return Promise.reject(GIIKER_NOBLEMSG);
            }
            var ret = Promise.resolve(true);
            if (window.navigator.bluetooth.getAvailability) {
                ret = window.navigator.bluetooth.getAvailability();
            }
            return ret.then(function (available) {
                if (!available) {
                    return Promise.reject(GIIKER_NOBLEMSG);
                }
            });
        },
        markSolved: function () {
            SmartCubeBridge._log('[giikerutil] markSolved called');
        },
        updateBattery: function (value) {
            SmartCubeBridge._log('[giikerutil] battery:', value);
        },
        reqMacAddr: function (forcePrompt, isWrongKey, deviceMac, defaultMac) {
            // GAN / QiYi / MoYu32 cubeではMAC取得にpromptを使用
            var savedMacMap = _savedMacMap;
            var deviceName = SmartCubeBridge.getDeviceName() || '';
            var mac = savedMacMap[deviceName];

            if (deviceMac) {
                if (mac && mac.toUpperCase() === deviceMac.toUpperCase()) {
                    // MAC一致
                } else {
                    mac = deviceMac;
                }
            } else {
                if (!mac || forcePrompt) {
                    mac = prompt(
                        (isWrongKey ? 'The MAC provided might be wrong!\n' : '') +
                        GIIKER_REQMACMSG,
                        mac || defaultMac || 'xx:xx:xx:xx:xx:xx'
                    );
                }
                if (!/^([0-9a-f]{2}[:-]){5}[0-9a-f]{2}$/i.test(mac)) {
                    return null;
                }
            }
            if (mac !== savedMacMap[deviceName]) {
                savedMacMap[deviceName] = mac;
                _savedMacMap = savedMacMap;
                try {
                    localStorage.setItem('smartcube_giiMacMap', JSON.stringify(savedMacMap));
                } catch (e) { }
            }
            return mac;
        },
        // bluetooth.jsのbluetoothutil.jsから参照される内部関数のスタブ
        _bridge_markSolved: null
    };
})();

// =============================================================================
// isaac.js の最小スタブ (mathlib.jsが乱数生成に使用)
// =============================================================================
var isaac = (function () {
    return {
        seed: function () { },
        random: function () { return Math.random(); }
    };
})();
