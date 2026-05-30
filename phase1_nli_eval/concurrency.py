"""Per-deployment rate limiting and 429/5xx backoff for Phase 1 parallel runs."""

from __future__ import annotations

import random
import threading
import time
from typing import Callable, TypeVar

import openai

RPM_PER_DEPLOYMENT: int = 200
MAX_CONCURRENCY: int = 10
MAX_429_RETRIES: int = 5

_limiters: dict[str, "RateLimiter"] = {}
_limiters_lock = threading.Lock()

T = TypeVar("T")


class RateLimiter:
    """Token-bucket rate limiter for a single deployment."""

    def __init__(self, rpm: int) -> None:
        self._tokens_per_sec = rpm / 60.0
        self._max_tokens = float(rpm)
        self._tokens = float(rpm)
        self._lock = threading.Lock()
        self._last_refill = time.monotonic()

    def acquire(self) -> None:
        while True:
            with self._lock:
                now = time.monotonic()
                elapsed = now - self._last_refill
                self._tokens = min(
                    self._max_tokens,
                    self._tokens + elapsed * self._tokens_per_sec,
                )
                self._last_refill = now
                if self._tokens >= 1.0:
                    self._tokens -= 1.0
                    return
                wait = (1.0 - self._tokens) / self._tokens_per_sec
            time.sleep(wait)


def get_limiter(deployment: str, rpm: int = RPM_PER_DEPLOYMENT) -> RateLimiter:
    """Return the process-wide shared limiter for *deployment*, creating it if needed."""
    with _limiters_lock:
        if deployment not in _limiters:
            _limiters[deployment] = RateLimiter(rpm)
        return _limiters[deployment]


def call_with_backoff(fn: Callable[[], T]) -> T:
    """Call *fn*, retrying on 429 / 5xx up to MAX_429_RETRIES times with exponential backoff."""
    for attempt in range(MAX_429_RETRIES + 1):
        try:
            return fn()
        except openai.RateLimitError:
            if attempt >= MAX_429_RETRIES:
                raise
        except openai.APIStatusError as e:
            if e.status_code < 500 or attempt >= MAX_429_RETRIES:
                raise
        delay = (2 ** attempt) + random.uniform(0.0, 1.0)
        time.sleep(delay)
    raise RuntimeError("unreachable")
