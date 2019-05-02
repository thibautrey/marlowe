import React from 'react';

function App() {
  return (
    <div>
      <div id="main">
        <div id="blocklyArea" />
        <div id="ui">
          <div id="codeAreaDiv" />
          <div id="actionButtons">
            <div class="row1">
              <button id="b2c" onClick="Haste.b2c()">
                -&gt; Blockly to Code
              </button>
              <button id="c2b" onClick="Haste.c2b()">
                Code to Blockly &lt;-
              </button>
              <button id="clear" onClick="Haste.clear_workspace()">
                Clear
              </button>
              <button id="execute" onClick="Haste.execute()">
                Execute
              </button>
            </div>
            <div class="row2">
              <button
                id="embedding"
                onClick="ifr=document.getElementById('iframe'); if (ifr == null) {var ifr=document.createElement('iframe');ifr.setAttribute('id', 'iframe');document.body.appendChild(ifr);ifr.setAttribute('src', 'editor/index.html');} else { ifr.style.display = 'block'; }"
              >
                Use Haskell embedding editor (Fay)
              </button>
            </div>
          </div>

          <br />
          <br />

          <div class="group">
            <h3 style={{ display: 'inline' }}>Current block:</h3>
            <input style={{ display: 'inline' }} type="number" id="currBlock" value="0" />
            <span class="highlight" />
            <span class="bar" />
          </div>

          <div>
            <h3>Contract state:</h3>
          </div>
          <div class="statusDiv" id="contractStateDiv" />
          <div>
            <h3>Input:</h3>
          </div>
          <div class="statusDiv" id="contractInputDiv" />
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
      <xml xmlns="http://www.w3.org/1999/xhtml" id="toolbox" style={{ display: 'none' }}>
        <category name="Observation">
          <block type="observation_trueobs" />
          <block type="observation_falseobs" />
          <block type="observation_notobs" />
          <block type="observation_orobs" />
          <block type="observation_andobs" />
          <block type="observation_belowtimeout">
            <field name="block_number">0</field>
          </block>
          <block type="observation_personchosesomething">
            <field name="choice_id">1</field>
            <field name="person">1</field>
          </block>
          <block type="observation_personchosethis">
            <field name="choice_id">1</field>
            <field name="person">1</field>
            <field name="choice_value">0</field>
          </block>
          <block type="observation_value_ge" />
        </category>
        <category name="Contract">
          <block type="contract_null" />
          <block type="contract_pay">
            <field name="pay_id">1</field>
            <field name="payer_id">1</field>
            <field name="payee_id">1</field>
            <field name="expiration">1</field>
          </block>
          <block type="contract_both" />
          <block type="contract_choice" />
          <block type="contract_when">
            <field name="timeout">0</field>
          </block>
          <block type="contract_commitcash">
            <field name="ccommit_id">1</field>
            <field name="person_id">1</field>
            <field name="end_expiration">0</field>
            <field name="start_expiration">0</field>
          </block>
          <block type="contract_redeemcc">
            <field name="ccommit_id">1</field>
          </block>
        </category>
        <category name="Money">
          <block type="value_available_money">
            <field name="commit_id">1</field>
          </block>
          <block type="value_add_money" />
          <block type="value_const_money">
            <field name="money">0</field>
          </block>
          <block type="money_from_choice">
            <field name="choice_id">1</field>
            <field name="person_id">1</field>
          </block>
        </category>
      </xml>
      <xml xmlns="http://www.w3.org/1999/xhtml" id="workspaceBlocks" style={{ display: 'none' }}>
        <variables />
        <block type="base_contract" id="brFRgBBnfL!JVLIp:jc#" x="13" y="187" />
      </xml>
      <script src="blocklyConfiguration.js" />
      <script src="marlowe.js" />
    </div>
  );
}

export default App;
