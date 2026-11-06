import Mathlib

theorem number_theory_313353 (a b c : ℚ) (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c) :
    ∃ q : ℚ, Real.sqrt ((1 / (a - b)^2) + (1 / (b - c)^2) + (1 / (c - a)^2)) = q := by 
  use abs (1 / (a - b) + 1 / (b - c) + 1 / (c - a))
  have h1 : ( (1 / (a - b)^2 : ℝ) + (1 / (b - c)^2 : ℝ) + (1 / (c - a)^2 : ℝ) ) =
    ( (1 / (a - b) + 1 / (b - c) + 1 / (c - a) : ℚ) )^2 := by
    have h2 : (a - b : ℝ) ≠ 0 := by exact_mod_cast (show a - b ≠ 0 by intro h; apply ha; linarith)
    have h3 : (b - c : ℝ) ≠ 0 := by exact_mod_cast (show b - c ≠ 0 by intro h; apply hb; linarith)
    have h4 : (c - a : ℝ) ≠ 0 := by exact_mod_cast (show c - a ≠ 0 by intro h; apply hc; linarith)
    field_simp [pow_two, h2, h3, h4]
    <;> nlinarith [pow_two_nonneg ( (1 / (a - b) + 1 / (b - c) + 1 / (c - a) : ℚ) ) ]
  rw [h1]
  rw [Real.sqrt_sq_eq_abs]
  norm_num [abs]
  <;> norm_num