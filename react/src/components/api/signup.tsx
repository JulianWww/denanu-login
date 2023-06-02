import {sha512} from 'crypto-hash';
import { Token } from './Token';

export function booleanToString(val?: boolean) {
  return val ? "true" : "false";
}

export async function signup(urlApi: string, handleError: (reason: string) => void, onSuccess: VoidFunction, username?: string, email?: string, password?: string, remember?: boolean, sendmail?: boolean) {
  if (username && email && password) {
    const data = await fetch(urlApi + "/signup.php?" + new URLSearchParams({
      username: username,
      mail: email,
      remember: booleanToString(remember),
      password: await sha512(password),
      sendmail: booleanToString(sendmail),
    }))
    .then(r => r.json());

    if (data.status === "success") {
      onSuccess();
    }
    else if (data.status === "fail") {
      handleError(data.reason)
    }
  }
}