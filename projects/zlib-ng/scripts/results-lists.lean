import ZlibNgF.Results

/-! Print the lists of `ZlibNgF/Results.lean` as Lean evaluates them, one `<list> <goal>` line each, for
`scripts/verification.py`: `lake env lean --run scripts/results-lists.lean`. -/

def main : IO Unit := do
  for (g, _) in ZlibNgF.Results.proved do IO.println s!"proved {g}"
  for g in ZlibNgF.Results.notDone do IO.println s!"notDone {g}"
  for g in ZlibNgF.Results.required do IO.println s!"required {g}"
