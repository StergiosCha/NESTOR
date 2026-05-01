"""Shared Azure LLM client setup.

Two endpoint flavours behind a single chat-completions call:
  - get_azure_client(): AzureOpenAI SDK for GPT deployments.
  - get_ai_client():    OpenAI SDK pointed at the Azure AI inference endpoint
                        (Llama, DeepSeek, Mistral on Azure AI).

call_llm() takes either client and uses the OpenAI chat-completions contract.
"""

import os

from openai import AzureOpenAI, OpenAI

def get_azure_client():
    return AzureOpenAI(
        api_version=os.environ.get("AZURE_OPENAI_API_VERSION", ""),
        azure_endpoint=os.environ.get("AZURE_OPENAI_ENDPOINT", ""),
        api_key=os.environ.get("AZURE_API_KEY", ""),
    )


def get_ai_client():
    return OpenAI(
        base_url=os.environ.get("AZURE_AI_ENDPOINT", ""),
        api_key=os.environ.get("AZURE_API_KEY", ""),
    )


def call_llm(client, model, messages, max_tokens, temperature=0.0):
    resp = client.chat.completions.create(
        model=model,
        messages=messages,
        temperature=temperature,
        max_tokens=max_tokens,
    )
    return resp.choices[0].message.content
