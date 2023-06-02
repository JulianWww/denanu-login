import { Token } from "./Token";

type urlValue = string | null;

export async function registerFunc (
  urlApi: string, 
  handleError: (reason: string) => void, 
  onSuccess: VoidFunction, 
  setToken: (token: Token, remember: boolean) => void, 
  username: urlValue, 
  mail: urlValue, 
  password: urlValue, 
  sendmail: urlValue,
  remember: urlValue, 
  signature: urlValue
  ) {
  
  if (username && mail && password && sendmail && signature) {
    console.log(
      username
    )

    const data = await fetch(urlApi + "/register.php?" + new URLSearchParams({
      username: username,
      mail: mail,
      password: password,
      sendmail: sendmail,
      signature: signature
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
  handleError("error")
}