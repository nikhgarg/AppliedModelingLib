/-!
Emit the transitive module closure already loaded by Lean for a generated
driver that imports one exact paper interface. This file is a command fragment:
the Python driver prepends the target import and `import Lean`, then appends the
command invocation. Python may resolve the emitted module names to source bytes,
but it must not reconstruct closure membership from source syntax.
-/

open Lean Elab Command

elab "#econcslib_import_closure" : command => do
  let env <- getEnv
  let modules := env.header.moduleNames.map fun name => Json.str name.toString
  let payload := Json.mkObj [
    ("schema", Json.str "econcslib.lean-loaded-module-closure/v1"),
    ("modules", Json.arr modules)
  ]
  liftIO <| IO.println s!"APPLIEDMODELINGLIB_LEAN_IMPORT_CLOSURE {payload.compress}"
