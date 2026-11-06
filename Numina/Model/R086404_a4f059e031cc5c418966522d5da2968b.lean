import Mathlib

theorem algebra_62007 {x : ℕ} (hx : x ≠ 0) (h : (1 + 40 / 100 : ℝ) * x * (1 - 20 / 100 : ℝ) = x + 21) :
    x = 175 := by
  have hx1 : (x : ℝ) = 175 := by
    norm_num at h ⊢
    -- After norm_num, h should be a linear equation (or perhaps a quadratic) which can be solved.
    -- From h:
    -- ((140/100) * (80/100) - (100/100)) * (x : ℝ) - (2100/100) = 0
    -- So the equation is of the form: ((140/100) * (80/100) - (100/100)) * x - (2100/100) = 0
    nlinarith [sq_nonneg ((x : ℝ)), sq_nonneg ((x : ℝ) - 175)]
  have hx2 : x = 175 := by
    exact_mod_cast hx1
  exact hx2