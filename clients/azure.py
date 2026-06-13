"""Shared LLM client setup.

Three endpoint flavours behind a single chat-completions call:
  - get_azure_openai_client(): AzureOpenAI SDK for GPT deployments (provider "azure-openai").
  - get_azure_ai_client():     OpenAI SDK pointed at the Azure AI inference endpoint
                               (provider "azure-ai" for Llama, DeepSeek, Mistral, Phi).
  - get_krikri_client():       OpenAI SDK pointed at the ILSP LiteLLM proxy
                               (provider "krikri" — requires LITELLM_HOST + LITELLM_ILSP_EVAL_API_KEY).

get_client(model_name) auto-selects the right client from the MODELS registry.
call_llm() takes any client and uses the OpenAI chat-completions contract
"""

import os

from openai import AzureOpenAI, OpenAI
from clients.models import MODELS

# Required environment variables per provider.
PROVIDER_ENV_VARS = {
    "azure-openai": ("AZURE_OPENAI_API_VERSION", "AZURE_OPENAI_ENDPOINT", "AZURE_API_KEY"),
    "azure-ai":     ("AZURE_AI_ENDPOINT", "AZURE_API_KEY"),
    "krikri":       ("LITELLM_HOST", "LITELLM_ILSP_EVAL_API_KEY"),
    "azure-gpt-5.4-pro":   ("GPT_5_4_PRO_ENDPOINT", "GPT_5_4_PRO_API_KEY"),
}


def assert_env(provider: str) -> None:
    required = PROVIDER_ENV_VARS.get(provider)
    if required is None:
        raise ValueError(
            f"Unknown provider '{provider}'"
        )
    missing = [v for v in required if not os.environ.get(v)]
    if missing:
        raise EnvironmentError(
            f"Provider '{provider}' missing required environment variables: {', '.join(missing)}"
        )


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
        timeout=60,
    )


def get_krikri_client():
    host = os.environ.get("LITELLM_HOST", "").rstrip("/")
    return OpenAI(
        base_url=f"{host}/v1",
        api_key=os.environ.get("LITELLM_ILSP_EVAL_API_KEY", ""),
    )


def get_client(model_name: str):
    if model_name not in MODELS:
        return get_azure_ai_client()
    provider = MODELS[model_name]["provider"]
    if provider == "azure-openai":
        return get_azure_openai_client()
    if provider == "krikri":
        return get_krikri_client()
    if provider == "azure-gpt-5.4-pro":
        return None
    return get_azure_ai_client()


def call_llm(client, model, messages, max_tokens, temperature=0.0):
    deployment = MODELS[model]["deployment"] if model in MODELS else model

    if model == "gpt-5.4-pro":
        import requests
        url = os.environ.get("GPT_5_4_PRO_ENDPOINT", "")
        headers = {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {os.environ.get('GPT_5_4_PRO_API_KEY', '')}",
        }
        data = {
            "input": messages,
            "max_output_tokens": max_tokens,
            "model": deployment,
        }
        resp = requests.post(url, headers=headers, json=data, timeout=(10, 60))
        resp.raise_for_status()

        return resp.json()["output"][1]["content"][0]["text"]
    
    else:
        resp = client.chat.completions.create(
            model=deployment,
            messages=messages,
            temperature=temperature,
            max_completion_tokens=max_tokens,
        )
        return resp.choices[0].message.content
