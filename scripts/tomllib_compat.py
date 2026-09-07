"""Expose a ``tomllib``-compatible parser on every supported Python runtime.

Python 3.11 added :mod:`tomllib` to the standard library.  Local release and
audit work also supports Python 3.10, where we prefer the API-compatible
``tomli`` backport and otherwise adapt the already-supported ``toml`` package.
Callers import the exported ``tomllib`` object and keep the standard-library
API and exception name.
"""

from __future__ import annotations

_INSTALL_HINT = (
    "Python 3.10 requires a TOML parser; run "
    "`python3 -m pip install -r requirements.txt` (or install `tomli`)."
)


try:  # Python 3.11 and newer.
    import tomllib as tomllib
    _backend_problem: str | None = None
except ModuleNotFoundError:  # Python 3.10.
    try:
        import tomli as tomllib  # type: ignore[no-redef]
        _backend_problem = None
    except ModuleNotFoundError:
        try:
            import toml as _toml
        except ModuleNotFoundError:

            class _UnavailableTomllib:
                class TOMLDecodeError(ValueError):
                    """Placeholder preserving the standard exception attribute."""

                @staticmethod
                def load(_stream: object) -> object:
                    raise ModuleNotFoundError(_INSTALL_HINT)

                @staticmethod
                def loads(_source: str) -> object:
                    raise ModuleNotFoundError(_INSTALL_HINT)

            tomllib = _UnavailableTomllib()  # type: ignore[assignment]
            _backend_problem = _INSTALL_HINT
        else:

            class _TomllibCompat:
                TOMLDecodeError = _toml.TomlDecodeError
                loads = staticmethod(_toml.loads)

                @staticmethod
                def load(stream: object) -> object:
                    read = getattr(stream, "read", None)
                    if not callable(read):
                        raise TypeError("tomllib.load() requires a binary file object")
                    source = read()
                    if not isinstance(source, bytes):
                        raise TypeError("tomllib.load() requires a binary file object")
                    return _toml.loads(source.decode("utf-8"))

            tomllib = _TomllibCompat()  # type: ignore[assignment]
            _backend_problem = None


def tomllib_dependency_problem() -> str | None:
    """Return the actionable Python 3.10 dependency error, if any."""

    return _backend_problem


__all__ = ["tomllib", "tomllib_dependency_problem"]
