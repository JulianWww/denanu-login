import * as React from 'react';
import { Theme } from '@mui/material';
interface SignUpProps {
    emailUpdates?: boolean;
    backendLocation: string;
    theme: Partial<Theme> | ((outerTheme: Theme) => Theme);
    loginUrl?: string;
}
export default function SignUp(props: SignUpProps): React.JSX.Element;
export {};
