import Mathlib

theorem algebra_305346 : ∏ m in (Finset.Ico (-7) 10).filter (fun x => IsSquare (x^2 + x + 7)), m = 84 := by
  native_decide