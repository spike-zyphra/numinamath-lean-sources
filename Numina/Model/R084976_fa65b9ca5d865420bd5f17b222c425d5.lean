import Mathlib

theorem algebra_286699 (a : Fin 5 → ℝ) (ha : a 0 = 10 ∧ a 1 = 4 ∧ a 2 = 8 ∧ a 3 = 7 ∧ a 4 = 6) :
    (a 0 + a 1 + a 2 + a 3 + a 4) / 5 = 7 := by
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4⟩
  rw [ha0, ha1, ha2, ha3, ha4]
  norm_num