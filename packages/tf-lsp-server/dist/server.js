import { createConnection, ProposedFeatures } from 'vscode-languageserver/node.js';
const connection = createConnection(ProposedFeatures.all);
connection.onInitialize((_params) => {
    return {
        capabilities: {}
    };
});
connection.onInitialized(() => {
    // Reserved for future initialization steps.
});
connection.listen();
