import * as React from 'react';
import Avatar from '@mui/material/Avatar';
import Button from '@mui/material/Button';
import TextField from '@mui/material/TextField';
import FormControlLabel from '@mui/material/FormControlLabel';
import Checkbox from '@mui/material/Checkbox';
import Link from '@mui/material/Link';
import Grid from '@mui/material/Grid';
import Box from '@mui/material/Box';
import LockOutlinedIcon from '@mui/icons-material/LockOutlined';
import Typography from '@mui/material/Typography';
import Container from '@mui/material/Container';
import { signin } from '../api/signin';
import useToken from '../api/Token';
import { Theme, ThemeProvider } from '@mui/material/styles';

export interface SinginProps {
  backendLocation: string;
  onLogIn?: VoidFunction;
  theme: Partial<Theme> | ((outerTheme: Theme) => Theme);
  signupUrl?: string;
}

export default function DenanuSignin(props: SinginProps) {
  const { backendLocation, onLogIn, theme, signupUrl } = props;

  const [ unameError, setUnameError ] = React.useState(false);
  const [ pswrdError, setPswrdError ] = React.useState(false);

  const [ unameErrorMsg, setUnameErrorMsg ] = React.useState<string | undefined>(undefined);

  const [, setToken ] = useToken()

  const handleSubmit = (event: React.FormEvent<HTMLFormElement>) => {
    event.preventDefault();
    const data = new FormData(event.currentTarget);
    
    const uname = data.get("user-name")?.toString();
    const pswrd = data.get("password")?.toString();
    const memo = data.get("remember")?.valueOf() as boolean | undefined;

    setUnameError(uname === "");
    setPswrdError(pswrd === "");

    signin(
      backendLocation, 
      reason => {
        if (reason === "uname missing") {
          setUnameErrorMsg("Username does not exists");
        }
      },
      () => {
        if (onLogIn)
          onLogIn();
      },
      setToken,
      uname,
      pswrd, 
      memo
    );
  };

  return (
    <ThemeProvider theme={theme}>
      <Container component="main" maxWidth="xs">
        <Box
          sx={{
            marginTop: 8,
            display: 'flex',
            flexDirection: 'column',
            alignItems: 'center',
          }}
        >
          <Avatar sx={{ m: 1, bgcolor: 'secondary.main' }}>
            <LockOutlinedIcon />
          </Avatar>
          <Typography component="h1" variant="h5">
            Sign in
          </Typography>
          <Box component="form" onSubmit={handleSubmit} noValidate sx={{ mt: 1 }}>
            <TextField
              margin="normal"
              required
              fullWidth
              id="user-name"
              label="User Name"
              name="user-name"
              autoComplete="user-name"
              autoFocus
              error={unameError || Boolean(unameErrorMsg)}
              helperText={unameErrorMsg}
            />
            <TextField
              margin="normal"
              required
              fullWidth
              name="password"
              label="Password"
              type="password"
              id="password"
              autoComplete="current-password"
              error={pswrdError}
            />
            <FormControlLabel
              control={<Checkbox value={true} color="primary" />}
              label="Remember me"
              name="remember"
            />
            <Button
              type="submit"
              fullWidth
              variant="contained"
              sx={{ mt: 3, mb: 2 }}
            >
              Sign In
            </Button>
            <Grid container>
              <Grid item xs>
                <Link href="#" variant="body2">
                  Forgot password?
                </Link>
              </Grid>
              <Grid item>
                <Link href={signupUrl} variant="body2">
                  {"Don't have an account? Sign Up"}
                </Link>
              </Grid>
            </Grid>
          </Box>
        </Box>
      </Container>
    </ThemeProvider>
  );
}