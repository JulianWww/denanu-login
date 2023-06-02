export declare function getValue<T>(key: string): T | undefined;
export declare function useLocalStorage<T>(name: string): [T | undefined, (val?: T, remember?: boolean) => void];
export default function useToken(): [Token | undefined, (val?: Token | undefined, remember?: boolean | undefined) => void];
export interface Token {
    username: string;
    token: string;
}
export interface IToken {
    token?: Token;
    setToken: (t?: Token, remember?: boolean) => void;
}
