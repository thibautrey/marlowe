$(function() {
  $('#tabs').tabs({ active: 0 });
});

// Code Area
window.codeArea = CodeMirror(document.getElementById('codeAreaDiv'), {
  value:
    'CommitCash (IdentCC 1) 1\n           (ConstMoney 100)\n           10 200\n           (CommitCash (IdentCC 2) 2\n                       (ConstMoney 20)\n                       20 200\n                       (When (PersonChoseSomething (IdentChoice 1) 1)\n                             100\n                             (Both (RedeemCC (IdentCC 1) Null)\n                                   (RedeemCC (IdentCC 2) Null))\n                             (Pay (IdentPay 1) 2 1\n                                  (ConstMoney 20)\n                                  200\n                                  (Both (RedeemCC (IdentCC 1) Null)\n                                        (RedeemCC (IdentCC 2) Null))))\n                       (RedeemCC (IdentCC 1) Null))\n           Null',
  mode: 'text/x-haskell'
});
window.codeArea.setSize('100%', '100%');

// Contract state
window.contractState = CodeMirror(document.getElementById('contractStateDiv'), {
  value: '([],[])',
  mode: 'text/x-haskell',
  lineWrapping: true
});
window.contractState.setSize('100%', '100%');

// Contract input
window.contractInput = CodeMirror(document.getElementById('contractInputDiv'), {
  value: '([],[],[],[])',
  mode: 'text/x-haskell',
  lineWrapping: true
});
window.contractInput.setSize('100%', '100%');

// Contract output
window.contractOutput = CodeMirror(document.getElementById('contractOutputDiv'), {
  value: '',
  mode: 'text/x-haskell',
  lineWrapping: true
});
window.contractOutput.setSize('100%', '100%');
