"""Shared model registry for all NESTOR pipelines.

Each entry maps a human-readable key to:
  deployment : exact deployment name for the Azure API, or model id for the LiteLLM proxy
  provider   : "azure-openai" (AzureOpenAI SDK, GPT models)
               "azure-ai"     (OpenAI-compatible, Llama/DeepSeek/Mistral/Phi)
               "krikri"       (ILSP LiteLLM proxy — requires LITELLM_HOST + LITELLM_ILSP_EVAL_API_KEY)
"""

MODELS = {
    "gpt-4o": {
        "deployment": "gpt-4o",
        "provider": "azure-openai",
    },
    "deepseek-r1": {
        "deployment": "DeepSeek-R1",
        "provider": "azure-ai",
    },
    "llama-70b": {
        "deployment": "Llama-3.3-70B-Instruct",
        "provider": "azure-ai",
    },
    "llama-8b": {
        "deployment": "Llama-3.1-8B-Instruct",
        "provider": "azure-ai",
    },
    "krikri-8b": {
        "deployment": "llama-krikri-8b-instruct-v1.5",
        "provider": "krikri",
    },
}
