import { Token } from './Token';
export declare function booleanToString(val?: boolean): "true" | "false";
export declare function signin(urlApi: string, handleError: (reason: string) => void, onSuccess: VoidFunction, setToken: (token: Token, remember: boolean) => void, username?: string, password?: string, remember?: boolean): Promise<void>;
