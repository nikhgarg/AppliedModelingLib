import lean_signature_manifest_helper

/-!
This module preserves the stable compiled audit-helper import path while the
implementation lives in the receipt-pinned standalone helper used by audit
runners.  Keeping one implementation prevents the injected and compiled audit
commands from drifting apart.
-/
