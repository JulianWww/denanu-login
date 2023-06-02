import type { Meta, StoryObj } from "@storybook/react";
import Singup from "./signup";

// Default metadata of the story https://storybook.js.org/docs/react/api/csf#default-export
const meta: Meta<typeof Singup> = {
  title: "Components/DenanuSignup",
  component: Singup,
};

export default meta;

// The story type for the component https://storybook.js.org/docs/react/api/csf#named-story-exports
type Story = StoryObj<typeof Singup>;

export const banner: Story = {
  args: {
    emailUpdates: false,
    backendLocation: "http://localhost:8000"
  },
  argTypes: {
    emailUpdates: {
      table: {
        defaultValue: { summary: false },
      },
      control: { type: 'boolean' },
      description: "Show the E-mail update checkbox",
    },
    backendLocation: {
      description: "Url of the sever backend",
    }
  },
};

