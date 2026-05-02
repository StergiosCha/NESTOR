"""Shared Azure LLM client setup.

Two endpoint flavours behind a single chat-completions call:
  - get_azure_openai_client(): AzureOpenAI SDK for GPT deployments (provider "azure-openai").
  - get_azure_ai_client():     OpenAI SDK pointed at the Azure AI inference endpoint
                               (provider "azure-ai" for Llama, DeepSeek, Mistral, Phi).

get_client(model_name) auto-selects the right client from the MODELS registry.
call_llm() takes either client and uses the OpenAI chat-completions contract.
"""

import os

from openai import AzureOpenAI, OpenAI
from utils.models import MODELS

def get_azure_openai_client():
    return AzureOpenAI(
        api_version=os.environ.get("AZURE_OPENAI_API_VERSION", ""),
        azure_endpoint=os.environ.get("AZURE_OPENAI_ENDPOINT", ""),
        api_key=os.environ.get("AZURE_API_KEY", ""),
    )


def get_azure_ai_client():
    return OpenAI(
        base_url=os.environ.get("AZURE_AI_ENDPOINT", ""),
        api_key=os.environ.get("AZURE_API_KEY", ""),
    )


def get_client(model_name: str):
    if model_name not in MODELS:
        valid = ", ".join(sorted(MODELS))
        raise ValueError(f"Unknown model '{model_name}'. Valid keys: {valid}")
    provider = MODELS[model_name]["provider"]
    if provider == "azure-openai":
        return get_azure_openai_client()
    return get_azure_ai_client()


def call_llm(client, model, messages, max_tokens, temperature=0.0):
    resp = client.chat.completions.create(
        model=model,
        messages=messages,
        temperature=temperature,
        max_tokens=max_tokens,
    )
    return resp.choices[0].message.content
