import {sha512} from 'crypto-hash';
import { Token } from './Token';

export function booleanToString(val?: boolean) {
  return val ? "true" : "false";
}

export async function signin(urlApi: string, handleError: (reason: string) => void, onSuccess: VoidFunction, setToken: (token: Token, remember: boolean) => void, username?: string, password?: string, remember?: boolean) {
  if (username && password) {
    const data = await fetch(urlApi + "/signin.php?" + new URLSearchParams({
      username: username,
      password: await sha512(password),
    }))
    .then(r => r.json());

    
    if (data.status === "success") {
      setToken(data.data, Boolean(remember));
      onSuccess();
    }
    else if (data.status === "fail") {
      handleError(data.reason)
    }
  }
}