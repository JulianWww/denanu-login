import { useState } from 'react';

export function getValue<T>(key: string) {
  const str = localStorage.getItem(key);
  if (str) {
    const val: T = JSON.parse(str);
    return val
  }
  return undefined;
}

export function useLocalStorage<T>(name: string): [T | undefined, (val?: T, remember?: boolean) => void] {

  const [value, setValue] = useState(getValue<T>(name));

  const save = (userToken?: T, remember?: boolean) => {
    if (remember || remember === undefined) {
      if (userToken) {
        localStorage.setItem(name, JSON.stringify(userToken));
      }
      else {
        localStorage.removeItem(name);
      }
    }
    setValue(userToken);
  };

  return [
    value, save
  ]
}

export default function useToken() {
  return useLocalStorage<Token>("token");
}

export interface Token {
  username: string;
  token: string;
}

export interface IToken {
  token?: Token;
  setToken: (t?: Token, remember?: boolean) => void;
}