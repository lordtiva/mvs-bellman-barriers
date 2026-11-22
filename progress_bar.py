"""Clean dependency-free progress bar with elapsed time and ETA formatting."""

from __future__ import annotations

import time


def format_duration(seconds: float) -> str:
    s = max(0, int(round(seconds)))
    h, rem = divmod(s, 3600)
    m, sec = divmod(rem, 60)
    if h > 0:
        return f"{h:d}h {m:02d}m {sec:02d}s"
    return f"{m:02d}m {sec:02d}s"


class ProgressBar:
    """
    Prints clean single-line progress updates with bar, percentage, elapsed time,
    and estimated time to completion (ETA). Safe for both interactive TTY and
    redirected task log files (avoids flooding logs when total is large).
    """

    def __init__(self, label: str, total: int, width: int = 22, min_interval_sec: float = 2.0) -> None:
        self.label = label
        self.total = max(1, int(total))
        self.width = max(8, int(width))
        self.min_interval_sec = float(min_interval_sec)
        self.t0 = time.perf_counter()
        self.last_print_t = -1e9
        self.done = 0

    def update(self, increment: int = 1, suffix: str = "", force: bool = False) -> None:
        self.done = min(self.total, self.done + increment)
        now = time.perf_counter()
        is_end = self.done >= self.total
        if not force and not is_end and (now - self.last_print_t) < self.min_interval_sec and self.done > 1:
            return
        self.last_print_t = now
        elapsed = now - self.t0
        frac = self.done / self.total
        filled = int(round(self.width * frac))
        bar = "#" * filled + "-" * (self.width - filled)
        eta = (elapsed / self.done) * (self.total - self.done) if self.done > 0 else 0.0
        eta_str = "00m 00s" if is_end else format_duration(eta)
        extra = f" | {suffix}" if suffix else ""
        print(
            f"  [{self.label}] [{bar}] {self.done:>{len(str(self.total))}}/{self.total} "
            f"({100.0 * frac:5.1f}%) | transcurrido: {format_duration(elapsed)} | ETA: {eta_str}{extra}",
            flush=True,
        )

    def set_done(self, done_count: int, suffix: str = "", force: bool = False) -> None:
        inc = max(0, int(done_count) - self.done)
        self.update(increment=inc, suffix=suffix, force=force)
