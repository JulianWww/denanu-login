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
import { signup } from '../api/signup';
import useToken from '../api/Token';
import { SxProps, Theme, ThemeProvider } from '@mui/material';
import EmailIcon from '@mui/icons-material/Email';



interface SignUpProps {
  emailUpdates?: boolean;
  backendLocation: string;
  theme: Partial<Theme> | ((outerTheme: Theme) => Theme);
  loginUrl?: string;
}

export default function SignUp(props: SignUpProps) {
  const { emailUpdates, backendLocation, theme, loginUrl } = props;

  const [ unameError, setUnameError ] = React.useState(false);
  const [ emailError, setEmailError ] = React.useState(false);
  const [ pswrdError, setPswrdError ] = React.useState(false);
  const [ awaitAuthentication, setAwaitAuthentication ] = React.useState(false);

  const [ unameErrorMsg, setUnameErrorMsg ] = React.useState<string | undefined>(undefined);

  const handleSubmit = (event: React.FormEvent<HTMLFormElement>) => {
    event.preventDefault();
    const data = new FormData(event.currentTarget);

    const uname = data.get("user-name")?.toString();
    const email = data.get("email")?.toString();
    const pswrd = data.get("password")?.toString();
    const memo = data.get("remember")?.valueOf() as boolean | undefined;
    const sendmail = data.get("receiveEmails")?.toString() as boolean | undefined;
    setUnameErrorMsg(undefined);

    signup(
      backendLocation, 
      reason => {
        if (reason === "uname Exists") {
          setUnameErrorMsg("Username already exists");
        }
      },
      () => {
        setAwaitAuthentication(true);
      },
      uname, 
      email, 
      pswrd, 
      memo, 
      sendmail
    );

    setUnameError(uname === "");
    setEmailError(email === "");
    setPswrdError(pswrd === "");
  };

  const baseBoxSx: SxProps<Theme> = {
    marginTop: 8,
    display: 'flex',
    flexDirection: 'column',
    alignItems: 'center',
  }

  if (awaitAuthentication) {
    return (
      <ThemeProvider theme={theme}>
        <Container maxWidth="xs">
          <Box sx={baseBoxSx}>
            <Avatar sx={{ m: 1, bgcolor: 'secondary.main' }}>
              <EmailIcon />
            </Avatar>
            <Typography component="h1" variant="h5">
              E-Mail verification
            </Typography>
            Please verify your E-Mail
          </Box>
        </Container>
      </ThemeProvider>
    );
  }

  return (
    <ThemeProvider theme={theme}>
      <Container maxWidth="xs">
        <Box
          sx={baseBoxSx}
        >
          <Avatar sx={{ m: 1, bgcolor: 'secondary.main' }}>
            <LockOutlinedIcon />
          </Avatar>
          <Typography component="h1" variant="h5">
            Sign up
          </Typography>
          <Box component="form" noValidate onSubmit={handleSubmit} sx={{ mt: 3 }}>
            <Grid container spacing={2}>
              <Grid item xs={12}>
                <TextField
                  required
                  fullWidth
                  id="user-name"
                  label="User Name"
                  name="user-name"
                  autoComplete="user-name"
                  error={unameError || Boolean(unameErrorMsg)}
                  helperText={unameErrorMsg}
                />
              </Grid>
              <Grid item xs={12}>
                <TextField
                  required
                  fullWidth
                  id="email"
                  label="Email Address"
                  name="email"
                  autoComplete="email"
                  error={emailError}
                />
              </Grid>
              <Grid item xs={12}>
                <TextField
                  required
                  fullWidth
                  name="password"
                  label="Password"
                  type="password"
                  id="password"
                  autoComplete="new-password"
                  error={pswrdError}
                />
              </Grid>
              <Grid item xs={12}>
                <FormControlLabel
                  control={<Checkbox value={true} color="primary" />}
                  label="Remember me"
                  name="remember"
                />
              </Grid>
              {
                emailUpdates ?
                  <Grid item xs={12}>
                    <FormControlLabel
                      control={<Checkbox value={true} color="primary" />}
                      label="I want to receive inspiration, marketing promotions and updates via email."
                      name="receiveEmails"
                    />
                  </Grid>
                :
                  null
              }
            </Grid>
            <Button
              type="submit"
              fullWidth
              variant="contained"
              sx={{ mt: 3, mb: 2 }}
            >
              Sign Up
            </Button>
            <Grid container justifyContent="flex-end">
              <Grid item>
                <Link href={loginUrl} variant="body2">
                  Already have an account? Sign in
                </Link>
              </Grid>
            </Grid>
          </Box>
        </Box>
      </Container>
    </ThemeProvider>
  );
}