import useToken from "../api/Token";
import { registerFunc } from "../api/register";
import { useLocation } from "react-router-dom";


interface RegisterProps {
  backendLocation: string;
  onLogIn?: VoidFunction;
}

export default function R(props: RegisterProps) {
  const { onLogIn, backendLocation } = props;

  const [, setToken ] = useToken();
  const params = new URLSearchParams(window.location.search);
  registerFunc (
    backendLocation,
    (r: string) => {},
    () => {
      if (onLogIn)
        onLogIn()
    },
    setToken,
    params.get("username"),
    params.get("mail"),
    params.get("password"),
    params.get("sendmail"),
    params.get("remember"),
    params.get("signature"),
  )
  
  return null;
}