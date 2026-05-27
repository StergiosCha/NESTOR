"""Shared model registry for all NESTOR pipelines.

Single source of truth for model access. Each entry maps a human-readable key to:
  deployment : exact deployment name for the Azure API (TO BE FILLED IN)
  provider   : "azure-openai" (AzureOpenAI SDK — GPT family)
               "azure-ai"     (OpenAI-compatible Azure AI inference endpoint — everything else)
               "krikri"       (ILSP LiteLLM proxy — requires LITELLM_HOST + LITELLM_ILSP_EVAL_API_KEY)
  reasoning  : True for reasoning models
"""

MODELS = {
    "gpt-4o": {
        "deployment": "gpt-4o",
        "provider": "azure-openai",
        "reasoning": False,
    },
    "gpt-5.4-pro": {
        "deployment": "gpt-5.4-pro",
        "provider": "azure-openai",
        "reasoning": False,
    },
    "deepseek-r1": {
        "deployment": "DeepSeek-R1",
        "provider": "azure-ai",
        "reasoning": True,
    },
    "deepseek-v4-pro": {
        "deployment": "DeepSeek-V4-Pro",
        "provider": "azure-ai",
        "reasoning": False,
    },
    "llama-3.3-70b": {
        "deployment": "Llama-3.3-70B-Instruct",
        "provider": "azure-ai",
        "reasoning": False,
    },
    "llama-4-maverick": {
        "deployment": "Llama-4-Maverick-17B-128E-Instruct-FP8",
        "provider": "azure-ai",
        "reasoning": False,
    },
    "mistral-large-3": {
        "deployment": "Mistral-Large-3",
        "provider": "azure-ai",
        "reasoning": False,
    },
    "phi-4": {
        "deployment": "Phi-4",
        "provider": "azure-ai",
        "reasoning": False,
    },
    "grok-4-20": {
        "deployment": "grok-4-20-non-reasoning",
        "provider": "azure-ai",
        "reasoning": False,
    },
    "grok-4-20-reasoning": {
        "deployment": "grok-4-20-reasoning",
        "provider": "azure-ai",
        "reasoning": True,
    },
}
