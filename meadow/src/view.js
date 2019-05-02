import React, { Fragment } from 'react';
import { withStyles, Button, Input } from '@material-ui/core';

export const Code = function Code() {
  return <div id="codeAreaDiv" />;
};

export const ActionButtons = withStyles({
  ActionButtons: {
    marginTop: 5,
    display: 'grid',
    gridTemplateRows: 'max-content max-content',
    gridRowGap: '5px'
  },
  Row1: {
    display: 'grid',
    gridTemplateColumns: '1fr 1fr 1fr 1fr',
    gridColumnGap: '5px'
  }
})(function ActionButtons({ classes, blocktoCode, codeToBlock, clearWorkspace, execute }) {
  return (
    <div className={classes.ActionButtons}>
      <div className={classes.Wrapper}>
        <Button onClick={blocktoCode} variant="raised">
          -&gt; Blockly to Code
        </Button>
        <Button onClick={codeToBlock} variant="raised">
          Code to Blockly &lt;-
        </Button>
        <Button onClick={clearWorkspace} variant="raised">
          Clear
        </Button>
        <Button onClick={execute} variant="raised">
          Execute
        </Button>
      </div>
      <div>
        <Button
          variant="raised"
          onClick="ifr=document.getElementById('iframe'); if (ifr == null) {var ifr=document.createElement('iframe');ifr.setAttribute('id', 'iframe');document.body.appendChild(ifr);ifr.setAttribute('src', 'editor/index.html');} else { ifr.style.display = 'block'; }"
        >
          Use Haskell embedding editor (Fay)
        </Button>
      </div>
    </div>
  );
});

export const CurrentBlock = function CurrentBlock({ value }) {
  return (
    <div class="group">
      <h3 style={{ display: 'inline' }}>Current block:</h3>
      <Input value={value} type="number" />
      <span class="highlight" />
      <span class="bar" />
    </div>
  );
};

export const ContractState = function ContractState() {
  return (
    <Fragment>
      <div>
        <h3>Contract state:</h3>
      </div>
      <div class="statusDiv" id="contractStateDiv" />
    </Fragment>
  );
};

export const InputForContract = function InputForContract() {
  return (
    <Fragment>
      <div>
        <h3>Input:</h3>
      </div>
      <div class="statusDiv" id="contractInputDiv" />
    </Fragment>
  );
};

export const App = function App({ children }) {
  return (
    <div>
      <div id="main">
        <div id="blocklyArea" />
        <div id="ui">
          {children.code}
          {children.actionButtons}
          {children.currentBlock}
          {children.contractState}
          {children.input}

          <div id="tabs">
            <ul>
              <li>
                <a draggable="false" href="#tabs-1">
                  Smart interface
                </a>
              </li>
              <li>
                <a draggable="false" href="#tabs-2">
                  Manual interface
                </a>
              </li>
            </ul>
            <div id="tabs-1">
              <table style={{ width: '100%' }}>
                <thead>
                  <tr>
                    <th width="100%">
                      <b>Potential actions</b>
                    </th>
                    <th align="center" valign="middle">
                      <button onClick="Haste.refreshActions()">&nbsp;&nbsp;&nbsp;Refresh&nbsp;&nbsp;&nbsp;</button>
                    </th>
                  </tr>
                </thead>
                <tbody id="actions">
                  <tr>
                    <td align="center" valign="middle">
                      Loading...
                    </td>
                    <td />
                  </tr>
                </tbody>
              </table>
            </div>
            <div id="tabs-2">
              <ul>
                <li>
                  <p style={{ display: 'inline' }}>Person</p>
                  <input style={{ display: 'inline', width: '50px' }} type="number" id="commitsPerson" value="1" />
                  <p style={{ display: 'inline' }}>
                    <b>commits</b>
                  </p>
                  <input style={{ display: 'inline', width: '50px' }} type="number" id="commitsAmmount" value="0" />
                  <p style={{ display: 'inline' }}>ADA with ID</p>
                  <input style={{ display: 'inline', width: '50px' }} type="number" id="commitsID" value="1" />
                  <p style={{ display: 'inline' }}>to expire by</p>
                  <input style={{ display: 'inline', width: '50px' }} type="number" id="commitsExpiry" value="1" />
                  <button
                    id="commit"
                    onClick="Haste.commit(document.getElementById('commitsPerson').value,document.getElementById('commitsAmmount').value,document.getElementById('commitsID').value,document.getElementById('commitsExpiry').value)"
                  >
                    Add to input
                  </button>
                </li>
                <li>
                  <p style={{ display: 'inline' }}>Person</p>
                  <input style={{ display: 'inline', width: '50px' }} type="number" id="redeemsPerson" value="1" />
                  <p style={{ display: 'inline' }}>
                    <b>redeems</b>
                  </p>
                  <input style={{ display: 'inline', width: '50px' }} type="number" id="redeemsAmmount" value="0" />
                  <p style={{ display: 'inline' }}>ADA from ID</p>
                  <input style={{ display: 'inline', width: '50px' }} type="number" id="redeemsID" value="1" />
                  <button
                    id="redeem"
                    onClick="Haste.redeem(document.getElementById('redeemsPerson').value,document.getElementById('redeemsAmmount').value,document.getElementById('redeemsID').value)"
                  >
                    Add to input
                  </button>
                </li>
                <li>
                  <p style={{ display: 'inline' }}>Person</p>
                  <input style={{ display: 'inline', width: '50px' }} type="number" id="claimsPerson" value="1" />
                  <p style={{ display: 'inline' }}>
                    <b>claims</b>
                  </p>
                  <input style={{ display: 'inline', width: '50px' }} type="number" id="claimsAmmount" value="0" />
                  <p style={{ display: 'inline' }}>ADA from ID</p>
                  <input style={{ display: 'inline', width: '50px' }} type="number" id="claimsID" value="1" />
                  <button
                    id="claim"
                    onClick="Haste.claim(document.getElementById('claimsPerson').value,document.getElementById('claimsAmmount').value,document.getElementById('claimsID').value)"
                  >
                    Add to input
                  </button>
                </li>
                <li>
                  <p style={{ display: 'inline' }}>Person</p>
                  <input style={{ display: 'inline', width: '50px' }} type="number" id="choosesPerson" value="1" />
                  <p style={{ display: 'inline' }}>
                    <b>chooses value</b>
                  </p>
                  <input style={{ display: 'inline', width: '50px' }} type="number" id="choosesAmmount" value="0" />
                  <p style={{ display: 'inline' }}>for ID</p>
                  <input style={{ display: 'inline', width: '50px' }} type="number" id="choosesID" value="1" />
                  <button
                    id="choice"
                    onClick="Haste.choose(document.getElementById('choosesPerson').value,document.getElementById('choosesAmmount').value,document.getElementById('choosesID').value)"
                  >
                    Add to input
                  </button>
                </li>
              </ul>
            </div>
          </div>
          <div>
            <h3>Output:</h3>
          </div>
          <div class="statusDiv" id="contractOutputDiv" />
          <div>
            <h3>Examples:</h3>
            <div id="examplesButtons">
              <button id="example1" onClick="Haste.depositIncentive()">
                Deposit incentive
              </button>
              <button id="example2" onClick="Haste.crowdFunding()">
                Crowd-funding
              </button>
              <button id="example3" onClick="Haste.escrow()">
                Escrow
              </button>
            </div>
          </div>
          <div>
            <h3>Related resources:</h3>
          </div>
          <ul>
            <li>
              <a href="https://github.com/input-output-hk/marlowe">Marlowe's github repository</a>
            </li>
            <li>
              <a href="https://github.com/input-output-hk/marlowe/blob/master/docs/tutorial-v1.3/README.md">
                Tutorial for Marlowe 1.3 and Meadow
              </a>
            </li>
          </ul>
        </div>
      </div>
      <div id="blocklyDiv" style={{ position: 'absolute' }} />
    </div>
  );
};
