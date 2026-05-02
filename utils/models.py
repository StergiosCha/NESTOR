"""Shared model registry for all NESTOR pipelines.

Each entry maps a human-readable key to:
  deployment : exact deployment name for the Azure API
  provider   : "azure-openai" (AzureOpenAI SDK, GPT models)
               "azure-ai"     (OpenAI-compatible, Llama/DeepSeek/Mistral/Phi)
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
    }
}
