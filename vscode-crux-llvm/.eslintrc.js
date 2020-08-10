module.exports = {
    'env': {
        'es6': true,
        'node': true
    },
    'extends': [
        'eslint:recommended',
        'plugin:@typescript-eslint/eslint-recommended'
    ],
    'globals': {
        'Atomics': 'readonly',
        'SharedArrayBuffer': 'readonly'
    },
    'parser': '@typescript-eslint/parser',
    'parserOptions': {
        'ecmaVersion': 2018,
        'sourceType': 'module'
    },
    'plugins': [
        '@typescript-eslint'
    ],
    'rules': {
        'indent': [
            'error',
            4,
            { 'SwitchCase': 1 }
        ],
        'linebreak-style': [
            'error',
            'unix'
        ],
        'no-unused-vars': [
            'off'
        ],
        'quotes': [
            'error',
            'single'
        ],
        'semi': [
            'error',
            'never'
        ]
    }
}