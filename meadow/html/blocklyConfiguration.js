var blocklyArea = document.getElementById('blocklyArea');
var blocklyDiv = document.getElementById('blocklyDiv');
var workspaceBlocks = document.getElementById('workspaceBlocks');
var demoWorkspace = Blockly.inject(blocklyDiv, {
  media: 'blockly/media/',
  toolbox: document.getElementById('toolbox')
});
var onresize = function(e) {
  // Compute the absolute coordinates and dimensions of blocklyArea.
  var element = blocklyArea;
  var x = 0;
  var y = 0;
  do {
    x += element.offsetLeft;
    y += element.offsetTop;
    element = element.offsetParent;
  } while (element);
  // Position blocklyDiv over blocklyArea.
  blocklyDiv.style.left = x + 'px';
  blocklyDiv.style.top = y + 'px';
  blocklyDiv.style.width = blocklyArea.offsetWidth - 20 + 'px';
  blocklyDiv.style.height = blocklyArea.offsetHeight + 'px';
  Blockly.svgResize(demoWorkspace);
};
onresize();
window.addEventListener('resize', onresize, false);
$('#blocklyArea').on('elementResize', function() {
  onresize(null);
});
var blocks = [
  {
    type: 'observation_andobs',
    message0: 'AndObs %1 %2 and %3 %4',
    args0: [
      {
        type: 'input_dummy',
        align: 'CENTRE'
      },
      {
        type: 'input_value',
        name: 'observation1',
        check: 'observation',
        align: 'RIGHT'
      },
      {
        type: 'input_dummy'
      },
      {
        type: 'input_value',
        name: 'observation2',
        check: 'observation',
        align: 'RIGHT'
      }
    ],
    inputsInline: true,
    output: 'observation',
    colour: 230,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'observation_belowtimeout',
    lastDummyAlign0: 'RIGHT',
    message0: 'BelowTimeout %1 block %2',
    args0: [
      {
        type: 'input_dummy',
        align: 'CENTRE'
      },
      {
        type: 'field_number',
        name: 'block_number',
        value: 1,
        min: 0
      }
    ],
    inputsInline: false,
    output: 'observation',
    colour: 230,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'observation_falseobs',
    lastDummyAlign0: 'CENTRE',
    message0: 'FalseObs',
    output: 'observation',
    colour: 230,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'observation_notobs',
    message0: 'NotObs %1 %2',
    args0: [
      {
        type: 'input_dummy',
        align: 'CENTRE'
      },
      {
        type: 'input_value',
        name: 'observation',
        check: 'observation',
        align: 'RIGHT'
      }
    ],
    inputsInline: true,
    output: 'observation',
    colour: 230,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'observation_orobs',
    message0: 'OrObs %1 %2 or %3 %4',
    args0: [
      {
        type: 'input_dummy',
        align: 'CENTRE'
      },
      {
        type: 'input_value',
        name: 'observation1',
        check: 'observation',
        align: 'RIGHT'
      },
      {
        type: 'input_dummy'
      },
      {
        type: 'input_value',
        name: 'observation2',
        check: 'observation',
        align: 'RIGHT'
      }
    ],
    inputsInline: true,
    output: 'observation',
    colour: 230,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'observation_personchosesomething',
    lastDummyAlign0: 'RIGHT',
    message0: 'PersonChoseSomething %1 for choice with id %2 ... %3 person %4 chose something',
    args0: [
      {
        type: 'input_dummy',
        align: 'CENTRE'
      },
      {
        type: 'field_number',
        name: 'choice_id',
        value: 1,
        min: 0
      },
      {
        type: 'input_dummy',
        align: 'RIGHT'
      },
      {
        type: 'field_number',
        name: 'person',
        value: 1,
        min: 1
      }
    ],
    output: 'observation',
    colour: 230,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'observation_personchosethis',
    lastDummyAlign0: 'RIGHT',
    message0: 'PersonChoseThis %1 for choice with id %2 ... %3 person %4 %5 chose %6 num %7',
    args0: [
      {
        type: 'input_dummy',
        align: 'CENTRE'
      },
      {
        type: 'field_number',
        name: 'choice_id',
        value: 1,
        min: 0
      },
      {
        type: 'input_dummy'
      },
      {
        type: 'field_number',
        name: 'person',
        value: 1,
        min: 1
      },
      {
        type: 'input_dummy',
        align: 'RIGHT'
      },
      {
        type: 'input_dummy',
        align: 'CENTRE'
      },
      {
        type: 'field_number',
        name: 'choice_value',
        value: 0
      }
    ],
    output: 'observation',
    colour: 230,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'observation_timeabove',
    lastDummyAlign0: 'RIGHT',
    message0: 'TimeAbove %1 block %2',
    args0: [
      {
        type: 'input_dummy',
        align: 'CENTRE'
      },
      {
        type: 'field_number',
        name: 'block_number',
        value: 1,
        min: 0
      }
    ],
    output: 'observation',
    colour: 230,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'observation_trueobs',
    lastDummyAlign0: 'CENTRE',
    message0: 'TrueObs',
    output: 'observation',
    colour: 230,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'base_contract',
    message0: '%1 CONTRACT %2 %3',
    args0: [
      {
        type: 'input_dummy'
      },
      {
        type: 'input_statement',
        name: 'base_contract',
        check: 'contract',
        align: 'RIGHT'
      },
      {
        type: 'input_dummy'
      }
    ],
    inputsInline: false,
    colour: 0,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'contract_null',
    message0: 'Null',
    previousStatement: 'contract',
    colour: 0,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'contract_redeemcc',
    message0: 'RedeemCC %1 allow the commit %2 with id %3 %4 to be redeemed then %5 continue as %6',
    args0: [
      {
        type: 'input_dummy',
        align: 'CENTRE'
      },
      {
        type: 'input_dummy'
      },
      {
        type: 'field_number',
        name: 'ccommit_id',
        value: 0,
        min: 1
      },
      {
        type: 'input_dummy',
        align: 'RIGHT'
      },
      {
        type: 'input_dummy'
      },
      {
        type: 'input_statement',
        name: 'contract',
        check: 'contract'
      }
    ],
    previousStatement: 'contract',
    colour: 0,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'contract_pay',
    message0:
      'Pay %1 with id %2 %3 use money commited by %4 person with id %5 %6 to pay: %7 ADA to person with id %8 %9 if claimed before block %10 %11 continue as %12',
    args0: [
      {
        type: 'input_dummy',
        align: 'CENTRE'
      },
      {
        type: 'field_number',
        name: 'pay_id',
        value: 1,
        min: 1
      },
      {
        type: 'input_dummy'
      },
      {
        type: 'input_dummy',
        align: 'RIGHT'
      },
      {
        type: 'field_number',
        name: 'payer_id',
        value: 1,
        min: 1
      },
      {
        type: 'input_dummy',
        align: 'RIGHT'
      },
      {
        type: 'input_value',
        name: 'ammount',
        check: 'value',
        align: 'RIGHT'
      },
      {
        type: 'field_number',
        name: 'payee_id',
        value: 1,
        min: 1
      },
      {
        type: 'input_dummy',
        align: 'RIGHT'
      },
      {
        type: 'field_number',
        name: 'expiration',
        value: 1,
        min: 0
      },
      {
        type: 'input_dummy',
        align: 'RIGHT'
      },
      {
        type: 'input_statement',
        name: 'contract',
        check: 'contract'
      }
    ],
    previousStatement: 'contract',
    colour: 0,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'contract_both',
    message0: 'Both %1 enforce both %2 %3 and %4 %5',
    args0: [
      {
        type: 'input_dummy',
        align: 'CENTRE'
      },
      {
        type: 'input_dummy'
      },
      {
        type: 'input_statement',
        name: 'contract1',
        check: 'contract',
        align: 'RIGHT'
      },
      {
        type: 'input_dummy'
      },
      {
        type: 'input_statement',
        name: 'contract2',
        check: 'contract',
        align: 'RIGHT'
      }
    ],
    previousStatement: 'contract',
    colour: 0,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'contract_choice',
    message0: 'Choice %1 if observation %2 then continue as %3 %4 otherwise continue as %5 %6',
    args0: [
      {
        type: 'input_dummy',
        align: 'CENTRE'
      },
      {
        type: 'input_value',
        name: 'observation',
        check: 'observation'
      },
      {
        type: 'input_dummy'
      },
      {
        type: 'input_statement',
        name: 'contract1',
        check: 'contract',
        align: 'RIGHT'
      },
      {
        type: 'input_dummy'
      },
      {
        type: 'input_statement',
        name: 'contract2',
        check: 'contract',
        align: 'RIGHT'
      }
    ],
    previousStatement: 'contract',
    colour: 0,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'contract_commitcash',
    message0:
      'CommitCash %1 with id %2 %3 person with id %4 %5 may deposit %6 ADA redeemable on block %7 or after, %8 if money is committed before block %9 %10 continue as %11 otherwise continue as %12',
    args0: [
      {
        type: 'input_dummy',
        align: 'CENTRE'
      },
      {
        type: 'field_number',
        name: 'ccommit_id',
        value: 1,
        min: 1
      },
      {
        type: 'input_dummy'
      },
      {
        type: 'field_number',
        name: 'person_id',
        value: 1,
        min: 1
      },
      {
        type: 'input_dummy',
        align: 'RIGHT'
      },
      {
        type: 'input_value',
        name: 'ammount',
        check: 'value',
        align: 'RIGHT'
      },
      {
        type: 'field_number',
        name: 'end_expiration',
        value: 0,
        min: 0
      },
      {
        type: 'input_dummy',
        align: 'RIGHT'
      },
      {
        type: 'field_number',
        name: 'start_expiration',
        value: 0,
        min: 0
      },
      {
        type: 'input_dummy',
        align: 'RIGHT'
      },
      {
        type: 'input_statement',
        name: 'contract1',
        check: 'contract',
        align: 'RIGHT'
      },
      {
        type: 'input_statement',
        name: 'contract2',
        check: 'contract',
        align: 'RIGHT'
      }
    ],
    previousStatement: 'contract',
    colour: 0,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'contract_when',
    message0: 'When %1 as soon as observation %2 continue as %3 %4 if block is  %5 or higher continue as %6 %7',
    args0: [
      {
        type: 'input_dummy',
        align: 'CENTRE'
      },
      {
        type: 'input_value',
        name: 'observation',
        check: 'observation'
      },
      {
        type: 'input_dummy'
      },
      {
        type: 'input_statement',
        name: 'contract1',
        check: 'contract',
        align: 'RIGHT'
      },
      {
        type: 'field_number',
        name: 'timeout',
        value: 0,
        min: 0
      },
      {
        type: 'input_dummy'
      },
      {
        type: 'input_statement',
        name: 'contract2',
        check: 'contract',
        align: 'RIGHT'
      }
    ],
    previousStatement: 'contract',
    colour: 0,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'observation_value_ge',
    message0: 'ValueGE %1 %2 is greater or equal than %3 %4',
    args0: [
      {
        type: 'input_dummy',
        align: 'CENTRE'
      },
      {
        type: 'input_value',
        name: 'value1',
        check: 'value',
        align: 'RIGHT'
      },
      {
        type: 'input_dummy'
      },
      {
        type: 'input_value',
        name: 'value2',
        check: 'value',
        align: 'RIGHT'
      }
    ],
    inputsInline: true,
    output: 'observation',
    colour: 230,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'value_available_money',
    lastDummyAlign0: 'CENTRE',
    message0: 'AvailableMoney %1 money available from the commit with id: %2 %3',
    args0: [
      {
        type: 'input_dummy',
        align: 'CENTRE'
      },
      {
        type: 'input_dummy'
      },
      {
        type: 'field_number',
        name: 'commit_id',
        value: 1,
        min: 0
      }
    ],
    inputsInline: true,
    output: 'value',
    colour: 135,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'value_add_money',
    message0: 'AddMoney %1 %2 + %3 %4',
    args0: [
      {
        type: 'input_dummy',
        align: 'CENTRE'
      },
      {
        type: 'input_value',
        name: 'value1',
        check: 'value'
      },
      {
        type: 'input_dummy'
      },
      {
        type: 'input_value',
        name: 'value2',
        check: 'value'
      }
    ],
    inputsInline: true,
    output: 'value',
    colour: 135,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'value_const_money',
    message0: 'ConstMoney %1 %2 %3 ADA',
    args0: [
      {
        type: 'input_dummy',
        align: 'CENTRE'
      },
      {
        type: 'field_number',
        name: 'money',
        value: 0,
        min: 0
      },
      {
        type: 'input_dummy',
        align: 'CENTRE'
      }
    ],
    inputsInline: true,
    output: 'value',
    colour: 135,
    tooltip: '',
    helpUrl: ''
  },
  {
    type: 'money_from_choice',
    message0:
      'MoneyFromChoice %1 use value of choice with id: %2 %3 chosen by participant with id: %4 %5 if no choice was made use: %6',
    args0: [
      {
        type: 'input_dummy',
        align: 'CENTRE'
      },
      {
        type: 'field_number',
        name: 'choice_id',
        value: 1,
        min: 0
      },
      {
        type: 'input_dummy',
        align: 'RIGHT'
      },
      {
        type: 'field_number',
        name: 'person_id',
        value: 1,
        min: 1
      },
      {
        type: 'input_dummy',
        align: 'RIGHT'
      },
      {
        type: 'input_value',
        name: 'default',
        check: 'value',
        align: 'RIGHT'
      }
    ],
    inputsInline: false,
    output: 'value',
    colour: 135,
    tooltip: '',
    helpUrl: ''
  }
];
blocks.forEach(function(block) {
  Blockly.Blocks[block['type']] = {
    init: function() {
      this.jsonInit(block);
    }
  };
});
Blockly.Marlowe = new Blockly.Generator('Marlowe');
Blockly.Marlowe.init = function(workspace) {};
Blockly.Marlowe.replace = function(a, b) {};
Blockly.Marlowe.finish = function(code) {
  return code;
};
Blockly.Marlowe.scrub_ = function(block, code) {
  return code;
};
Blockly.Marlowe['observation_andobs'] = function(block) {
  var value_observation1 = Blockly.Marlowe.valueToCode(block, 'observation1', Blockly.Marlowe.ORDER_ATOMIC);
  var value_observation2 = Blockly.Marlowe.valueToCode(block, 'observation2', Blockly.Marlowe.ORDER_ATOMIC);
  var code = '(AndObs ' + value_observation1 + ' ' + value_observation2 + ')';
  return [code, 0];
};

Blockly.Marlowe['observation_belowtimeout'] = function(block) {
  var number_block_number = block.getFieldValue('block_number');
  var code = '(BelowTimeout ' + number_block_number + ')';
  return [code, 0];
};

Blockly.Marlowe['observation_falseobs'] = function(block) {
  var code = 'FalseObs';
  return [code, 0];
};

Blockly.Marlowe['observation_notobs'] = function(block) {
  var value_observation = Blockly.Marlowe.valueToCode(block, 'observation', Blockly.Marlowe.ORDER_ATOMIC);
  var code = '(NotObs ' + value_observation + ')';
  return [code, 0];
};

Blockly.Marlowe['observation_orobs'] = function(block) {
  var value_observation1 = Blockly.Marlowe.valueToCode(block, 'observation1', Blockly.Marlowe.ORDER_ATOMIC);
  var value_observation2 = Blockly.Marlowe.valueToCode(block, 'observation2', Blockly.Marlowe.ORDER_ATOMIC);
  var code = '(OrObs ' + value_observation1 + ' ' + value_observation2 + ')';
  return [code, 0];
};

Blockly.Marlowe['observation_personchosesomething'] = function(block) {
  var number_choice_id = block.getFieldValue('choice_id');
  var number_person = block.getFieldValue('person');
  var code = '(PersonChoseSomething (IdentChoice ' + number_choice_id + ') ' + number_person + ')';
  return [code, 0];
};

Blockly.Marlowe['observation_personchosethis'] = function(block) {
  var number_choice_id = block.getFieldValue('choice_id');
  var number_person = block.getFieldValue('person');
  var number_choice_value = block.getFieldValue('choice_value');
  var code =
    '(PersonChoseThis (IdentChoice ' + number_choice_id + ') ' + number_person + ' ' + number_choice_value + ')';
  return [code, 0];
};

Blockly.Marlowe['observation_trueobs'] = function(block) {
  var code = 'TrueObs';
  return [code, 0];
};

Blockly.Marlowe['base_contract'] = function(block) {
  var statements_name = Blockly.Marlowe.statementToCode(block, 'base_contract');
  var code = statements_name;
  return code;
};

Blockly.Marlowe['contract_null'] = function(block) {
  var code = 'Null';
  return code;
};

Blockly.Marlowe['contract_redeemcc'] = function(block) {
  var number_ccommit_id = block.getFieldValue('ccommit_id');
  var statements_contract = Blockly.Marlowe.statementToCode(block, 'contract');
  var code = '(RedeemCC (IdentCC ' + number_ccommit_id + ') ' + statements_contract + ')';
  return code;
};

Blockly.Marlowe['contract_pay'] = function(block) {
  var number_pay_id = block.getFieldValue('pay_id');
  var number_payer_id = block.getFieldValue('payer_id');
  var value_ammount = Blockly.Marlowe.valueToCode(block, 'ammount', Blockly.Marlowe.ORDER_ATOMIC);
  var number_payee_id = block.getFieldValue('payee_id');
  var number_expiration = block.getFieldValue('expiration');
  var statements_contract = Blockly.Marlowe.statementToCode(block, 'contract');
  var code =
    '(Pay (IdentPay ' +
    number_pay_id +
    ') ' +
    number_payer_id +
    ' ' +
    number_payee_id +
    ' ' +
    value_ammount +
    ' ' +
    number_expiration +
    ' ' +
    statements_contract +
    ')';
  return code;
};

Blockly.Marlowe['contract_both'] = function(block) {
  var statements_contract1 = Blockly.Marlowe.statementToCode(block, 'contract1');
  var statements_contract2 = Blockly.Marlowe.statementToCode(block, 'contract2');
  var code = '(Both ' + statements_contract1 + ' ' + statements_contract2 + ')';
  return code;
};

Blockly.Marlowe['contract_choice'] = function(block) {
  var value_observation = Blockly.Marlowe.valueToCode(block, 'observation', Blockly.Marlowe.ORDER_ATOMIC);
  var statements_contract1 = Blockly.Marlowe.statementToCode(block, 'contract1');
  var statements_contract2 = Blockly.Marlowe.statementToCode(block, 'contract2');
  var code = '(Choice ' + value_observation + ' ' + statements_contract1 + ' ' + statements_contract2 + ')';
  return code;
};
Blockly.Marlowe['contract_commitcash'] = function(block) {
  var number_ccommit_id = block.getFieldValue('ccommit_id');
  var number_person_id = block.getFieldValue('person_id');
  var value_ammount = Blockly.Marlowe.valueToCode(block, 'ammount', Blockly.Marlowe.ORDER_ATOMIC);
  var number_end_expiration = block.getFieldValue('end_expiration');
  var number_start_expiration = block.getFieldValue('start_expiration');
  var statements_contract1 = Blockly.Marlowe.statementToCode(block, 'contract1');
  var statements_contract2 = Blockly.Marlowe.statementToCode(block, 'contract2');
  var code =
    '(CommitCash (IdentCC ' +
    number_ccommit_id +
    ') ' +
    number_person_id +
    ' ' +
    value_ammount +
    ' ' +
    number_start_expiration +
    ' ' +
    number_end_expiration +
    ' ' +
    statements_contract1 +
    ' ' +
    statements_contract2 +
    ')';
  return code;
};

Blockly.Marlowe['contract_when'] = function(block) {
  var value_observation = Blockly.Marlowe.valueToCode(block, 'observation', Blockly.Marlowe.ORDER_ATOMIC);
  var statements_contract1 = Blockly.Marlowe.statementToCode(block, 'contract1');
  var number_timeout = block.getFieldValue('timeout');
  var statements_contract2 = Blockly.Marlowe.statementToCode(block, 'contract2');
  var code =
    '(When ' + value_observation + ' ' + number_timeout + ' ' + statements_contract1 + ' ' + statements_contract2 + ')';
  return code;
};

Blockly.Marlowe['observation_value_ge'] = function(block) {
  var value_value1 = Blockly.Marlowe.valueToCode(block, 'value1', Blockly.Marlowe.ORDER_ATOMIC);
  var value_value2 = Blockly.Marlowe.valueToCode(block, 'value2', Blockly.Marlowe.ORDER_ATOMIC);
  var code = '(ValueGE ' + value_value1 + ' ' + value_value2 + ')';
  return [code, 0];
};

Blockly.Marlowe['value_available_money'] = function(block) {
  var number_commit_id = block.getFieldValue('commit_id');
  var code = '(AvailableMoney (IdentCC ' + number_commit_id + '))';
  return [code, 0];
};

Blockly.Marlowe['value_add_money'] = function(block) {
  var value_value1 = Blockly.Marlowe.valueToCode(block, 'value1', Blockly.Marlowe.ORDER_ATOMIC);
  var value_value2 = Blockly.Marlowe.valueToCode(block, 'value2', Blockly.Marlowe.ORDER_ATOMIC);
  var code = '(AddMoney ' + value_value1 + ' ' + value_value2 + ')';
  return [code, 0];
};

Blockly.Marlowe['value_const_money'] = function(block) {
  var number_money = block.getFieldValue('money');
  var code = '(ConstMoney ' + number_money + ')';
  return [code, 0];
};

Blockly.Marlowe['money_from_choice'] = function(block) {
  var number_choice_id = block.getFieldValue('choice_id');
  var number_person_id = block.getFieldValue('person_id');
  var value_default = Blockly.Marlowe.valueToCode(block, 'default', Blockly.Marlowe.ORDER_ATOMIC);
  var code = '(MoneyFromChoice (IdentChoice ' + number_choice_id + ') ' + number_person_id + ' ' + value_default + ')';
  return [code, 0];
};

/* Load blocks to workspace. */
Blockly.Xml.domToWorkspace(workspaceBlocks, demoWorkspace);
demoWorkspace.getAllBlocks()[0].setDeletable(false);
