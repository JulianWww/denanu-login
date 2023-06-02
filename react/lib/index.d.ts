import * as React from 'react';
import { Theme } from '@mui/material/styles';
import { Theme as Theme$1 } from '@mui/material';

interface SinginProps {
    backendLocation: string;
    onLogIn?: VoidFunction;
    theme: Partial<Theme> | ((outerTheme: Theme) => Theme);
    signupUrl?: string;
}
declare function DenanuSignin(props: SinginProps): React.JSX.Element;

interface SignUpProps {
    emailUpdates?: boolean;
    backendLocation: string;
    theme: Partial<Theme$1> | ((outerTheme: Theme$1) => Theme$1);
    loginUrl?: string;
}
declare function SignUp(props: SignUpProps): React.JSX.Element;

interface RegisterProps {
    backendLocation: string;
    onLogIn?: VoidFunction;
}
declare function R(props: RegisterProps): null;

declare function getValue<T>(key: string): T | undefined;
declare function useLocalStorage<T>(name: string): [T | undefined, (val?: T, remember?: boolean) => void];
declare function useToken(): [Token | undefined, (val?: Token | undefined, remember?: boolean | undefined) => void];
interface Token {
    username: string;
    token: string;
}
interface IToken {
    token?: Token;
    setToken: (t?: Token, remember?: boolean) => void;
}

export { DenanuSignin as DenanuLogin, R as DenanuRegister, SignUp as DenanuSignup, IToken, Token, getValue, useLocalStorage, useToken };
