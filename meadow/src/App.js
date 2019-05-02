import { withObjectChildren, defaultValue, synced, number } from 'realue';
import { compose, withHandlers, withProps } from 'recompose';

import * as views from './view';
/*require('./marlowe');
require('./blocklyConfiguration');*/

const Code = compose()(views.Code);

const ActionButtons = compose(
  withHandlers({
    blockToCode: () => {},
    codeToBlock: () => {},
    clearWorkspace: () => {},
    execute: () => {}
  })
)(views.ActionButtons);

const CurrentBlock = compose(
  withProps({ defaultValue: 0 }),
  number,
  defaultValue,
  synced
)(views.CurrentBlock);

export default compose(
  withObjectChildren({
    actionButtons: [ActionButtons, ['value'], () => ({})],
    code: [Code, ['value'], () => ({})],
    currentBlock: [CurrentBlock, ['value'], () => ({})]
  })
)(views.App);
