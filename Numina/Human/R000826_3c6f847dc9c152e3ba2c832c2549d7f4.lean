import Mathlib

open Real Set
open scoped BigOperators

/- Find the minimum value of
\[\frac{x^2}{x - 8}\]for $x > 8.$ -/
theorem algebra_16876 : IsLeast {y : ℝ | ∃ x, y = x^2 / (x - 8) ∧ x > 8} 32 := by 
  refine' ⟨⟨16, by norm_num, by norm_num⟩, fun y hy ↦ _⟩
  obtain ⟨x, rfl, hx⟩ := hy
  rw [le_div_iff] <;>
    nlinarith [sq_nonneg (x - 16)]