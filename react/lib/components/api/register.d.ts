import { Token } from "./Token";
type urlValue = string | null;
export declare function registerFunc(urlApi: string, handleError: (reason: string) => void, onSuccess: VoidFunction, setToken: (token: Token, remember: boolean) => void, username: urlValue, mail: urlValue, password: urlValue, sendmail: urlValue, remember: urlValue, signature: urlValue): Promise<void>;
export {};
