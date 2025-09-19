import { Frame, Order, State } from '../../pilot-core/dist/index';
export interface RiskConfig {
    maxOrdersPerTick: number;
}
export declare function evaluate(state: State, orders: Order[], frame: Frame, config: RiskConfig): Order[];
export declare const riskSchemas: {
    config: {
        readonly type: "object";
        readonly additionalProperties: false;
        readonly properties: {
            readonly maxOrdersPerTick: {
                readonly type: "integer";
                readonly minimum: 0;
            };
        };
        readonly required: readonly ["maxOrdersPerTick"];
    };
};
