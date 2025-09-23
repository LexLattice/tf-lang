import { createConnection, ProposedFeatures, type InitializeParams, type InitializeResult } from 'vscode-languageserver/node.js';

const connection = createConnection(ProposedFeatures.all);

connection.onInitialize((_params: InitializeParams): InitializeResult => {
  return {
    capabilities: {}
  };
});

connection.onInitialized(() => {
  // Reserved for future initialization steps.
});

connection.listen();
