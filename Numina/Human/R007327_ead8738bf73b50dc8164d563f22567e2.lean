import Mathlib

/- The expression $\dfrac{\sqrt[4]{7}}{\sqrt[3]{7}}$ equals 7 raised to what power? -/
theorem algebra_10618 : (7 : ℝ) ^ ((1 : ℝ) / 4) / (7 ^ ((1 : ℝ) / 3)) = 7 ^ ((-1 : ℝ) / 12) := by 
  field_simp
  ring_nf
  <;> rw [← Real.rpow_add] <;> field_simp <;> ring