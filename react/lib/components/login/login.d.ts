import * as React from 'react';
import { Theme } from '@mui/material/styles';
export interface SinginProps {
    backendLocation: string;
    onLogIn?: VoidFunction;
    theme: Partial<Theme> | ((outerTheme: Theme) => Theme);
    signupUrl?: string;
}
export default function DenanuSignin(props: SinginProps): React.JSX.Element;
