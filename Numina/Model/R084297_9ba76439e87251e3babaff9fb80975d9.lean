import Mathlib

theorem algebra_5 (M W : Fin 6 → ℤ) (hM : ∀ i, M i = 57) (hW : ∀ i, W i = 52) :
    (6 * 57 + 9 * 52) / (6 + 9) = (6 * 57 + 9 * 52 : ℝ) / (6 + 9) ∧
    (6 * 57 + 9 * 52) / (6 + 9) = 54 := by
  constructor
  · -- Show that the integer division equals the real division
    norm_num
  · -- Compute the integer division and show it equals 54
    norm_num