export declare function booleanToString(val?: boolean): "true" | "false";
export declare function signup(urlApi: string, handleError: (reason: string) => void, onSuccess: VoidFunction, username?: string, email?: string, password?: string, remember?: boolean, sendmail?: boolean): Promise<void>;
