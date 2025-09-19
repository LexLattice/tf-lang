import { Frame, Order, State } from '@tf-lang/pilot-core';
export type StrategyName = 'momentum' | 'meanReversion';
export interface StrategyContext {
    nextId: () => string;
}
export interface StrategyImplementation {
    decide(state: State, frame: Frame, context: StrategyContext): Order[];
}
export declare function getStrategy(name: StrategyName): StrategyImplementation;
export interface RunOptions {
    strategy: StrategyName;
    frames: Frame[];
    seed: number | string;
    initialState?: State;
}
export interface RunResult {
    orders: Order[];
    state: State;
}
export declare function runStrategy(options: RunOptions): RunResult;
export declare function readFrames(path: string): Promise<Frame[]>;
export declare function writeOrders(path: string, orders: Order[]): Promise<void>;
