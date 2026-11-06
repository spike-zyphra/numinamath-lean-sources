import Mathlib

theorem algebra_4897 {x y : ℕ} (hyx : y < x) (hx : x > 0) (hy : y > 0)
    (hquot : (x : ℝ) / y = 5 / 2) (hprod : x * y = 160) :
    x = 20 := by
  have h1 : (x : ℝ) > 0 := by exact_mod_cast hx
  have h2 : (y : ℝ) > 0 := by exact_mod_cast hy
  have h3 : (x : ℝ) / (y : ℝ) = 5 / 2 := by
    exact_mod_cast hquot
  have h4 : 2 * (x : ℝ) = 5 * (y : ℝ) := by
    field_simp at h3
    nlinarith
  have h5 : 2 * x = 5 * y := by
    exact_mod_cast h4
  have h6 : x ≤ 80 := by
    nlinarith [show y ≥ 1 by linarith, hprod]
  have h7 : x = 20 := by
    interval_cases x <;> omega
  exact h7