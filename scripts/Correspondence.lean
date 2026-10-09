import Ratpoints.Model
import Lean

/-!
# The declarations of the model and their docstrings

Writes every declaration of the model (the module `Ratpoints.Model` and the modules below it)
that has a docstring of its own to a JSON file, as an array of objects with the fields `name`
(for a private declaration, the name it was declared with), `private`, `module`, `line` (the line
of the declaration in its source file) and `doc`. A docstring that `@[inherit_doc]` lends to a
notation or an alias is not the declaration's own, so it never makes a second record. The file is
the one named by the environment variable `CORRESPONDENCE_DECLS`, by default
`.lake/correspondence-decls.json`.

`scripts/correspondence.py` runs this file with `lake env lean scripts/Correspondence.lean`,
after `lake build RatpointsModel`, and reads the `C:` and `Deviation:` paragraphs of the
docstrings; `correspondence/README.md` describes the record. Reading the docstrings from the
environment rather than from the source text gives the full names of the declarations, so every
name in the record exists by construction.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let path := (← IO.getEnv "CORRESPONDENCE_DECLS").getD ".lake/correspondence-decls.json"
  let mut decls : Array (String × Json) := #[]
  for (name, _) in env.constants.toList do
    let user := privateToUserName name
    if user.isInternal then continue
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    unless (`Ratpoints.Model).isPrefixOf mod do continue
    let some doc := docStringExt.find? (level := .server) env name | continue
    let line := match ← liftCoreM (findDeclarationRanges? name) with
      | some r => toJson r.range.pos.line
      | none => Json.null
    decls := decls.push (user.toString, Json.mkObj
      [("name", toJson user.toString), ("private", toJson (isPrivateName name)),
        ("module", toJson mod.toString), ("line", line), ("doc", toJson doc)])
  let sorted := decls.qsort (fun a b ↦ a.1 < b.1) |>.map (·.2)
  IO.FS.writeFile path ((Json.arr sorted).pretty ++ "\n")
  logInfo m!"wrote {sorted.size} declarations of the model to {path}"
