import Mathlib

theorem other_188050 : (Nat.card {x | x = 1}) = 1 := by
  have h : {x : ℕ | x = 1} = {1} := by
    ext x
    simp
  rw [h]
  simp