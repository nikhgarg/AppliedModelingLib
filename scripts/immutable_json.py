"""Recursively immutable, ``dict``/``list``-compatible JSON snapshots.

Current evidence transactions pass exact parsed inputs through validators that
historically require concrete ``dict`` and ``list`` values.  These containers
preserve that read interface while rejecting every mutation operation.  The
module contains no audit policy or acceptance decision.
"""

from __future__ import annotations

import copy
from typing import Any


def _immutable_json_error(*_args: object, **_kwargs: object) -> None:
    raise TypeError("evidence run snapshots are immutable")


class FrozenJSONDict(dict[str, Any]):
    """A ``dict``-compatible recursive read view for existing validators."""

    __setitem__ = _immutable_json_error
    __delitem__ = _immutable_json_error
    clear = _immutable_json_error
    pop = _immutable_json_error
    popitem = _immutable_json_error
    setdefault = _immutable_json_error
    update = _immutable_json_error
    __ior__ = _immutable_json_error

    def __copy__(self) -> dict[str, Any]:
        return dict(self)

    def __deepcopy__(self, memo: dict[int, Any]) -> dict[str, Any]:
        return copy.deepcopy(dict(self), memo)


class FrozenJSONList(list[Any]):
    """A ``list``-compatible recursive read view for existing validators."""

    __setitem__ = _immutable_json_error
    __delitem__ = _immutable_json_error
    append = _immutable_json_error
    clear = _immutable_json_error
    extend = _immutable_json_error
    insert = _immutable_json_error
    pop = _immutable_json_error
    remove = _immutable_json_error
    reverse = _immutable_json_error
    sort = _immutable_json_error
    __iadd__ = _immutable_json_error
    __imul__ = _immutable_json_error

    def __copy__(self) -> list[Any]:
        return list(self)

    def __deepcopy__(self, memo: dict[int, Any]) -> list[Any]:
        return copy.deepcopy(list(self), memo)


_FROZEN_DICT_SUBCLASS_BY_BASE: dict[type[Any], type[dict[str, Any]]] = {}


def _frozen_dict_subclass(base: type[Any]) -> type[dict[str, Any]]:
    """Preserve private loader-token subclasses while disabling mutation."""

    if base is dict or base is FrozenJSONDict:
        return FrozenJSONDict
    cached = _FROZEN_DICT_SUBCLASS_BY_BASE.get(base)
    if cached is not None:
        return cached
    attributes = {
        "__slots__": (),
        "__setitem__": _immutable_json_error,
        "__delitem__": _immutable_json_error,
        "clear": _immutable_json_error,
        "pop": _immutable_json_error,
        "popitem": _immutable_json_error,
        "setdefault": _immutable_json_error,
        "update": _immutable_json_error,
        "__ior__": _immutable_json_error,
        "__copy__": FrozenJSONDict.__copy__,
        "__deepcopy__": FrozenJSONDict.__deepcopy__,
        "__module__": __name__,
    }
    frozen = type(f"Frozen{base.__name__}", (base,), attributes)
    _FROZEN_DICT_SUBCLASS_BY_BASE[base] = frozen
    return frozen


def freeze_json(value: Any, *, preserve_dict_subclasses: bool = False) -> Any:
    """Return a recursively immutable JSON-compatible value."""

    if isinstance(value, dict):
        frozen_type = (
            _frozen_dict_subclass(type(value))
            if preserve_dict_subclasses
            else FrozenJSONDict
        )
        return frozen_type(
            {
                str(key): freeze_json(
                    item,
                    preserve_dict_subclasses=preserve_dict_subclasses,
                )
                for key, item in value.items()
            }
        )
    if isinstance(value, list):
        return FrozenJSONList(
            freeze_json(
                item,
                preserve_dict_subclasses=preserve_dict_subclasses,
            )
            for item in value
        )
    return value
