import Mathlib

theorem algebra_21749 : ((Finset.range 10).filter fun n => n ∣ (60 + n)).card = 6 := by
  rfl