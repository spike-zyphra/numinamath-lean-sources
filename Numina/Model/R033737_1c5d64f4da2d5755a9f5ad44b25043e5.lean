import Mathlib

theorem algebra_180971 {x : ℝ} (hx : x > 0) (h : 11.15 * Real.sqrt ((1 + x) / x) + 1 / x = 5) :
    x = 1 / 3 := by
  have h1 : Real.sqrt ((1 + x) / x) ≥ 0 := by positivity
  have h2 : 11.15 * Real.sqrt ((1 + x) / x) ≥ 0 := by
    positivity
  have h3 : 1 / x > 0 := by 
    apply div_pos 
    norm_num
    all_goals linarith
  have h5 : Real.sqrt ((1 + x) / x) ≥ 1 := by
    have h6 : (1 + x) / x ≥ 1 := by
      have h7 : x > 0 := hx
      apply (le_div_iff₀ (by linarith)).mpr
      nlinarith
    have h8 : Real.sqrt ((1 + x) / x) ≥ Real.sqrt (1 : ℝ) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h9 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
    nlinarith [h8, h9]
  have h10 : 11.15 * Real.sqrt ((1 + x) / x) ≥ 11.15 := by
    nlinarith [h5]
  have h11 : 11.15 * Real.sqrt ((1 + x) / x) + 1 / x > 5 := by
    nlinarith [h3, h10]
  linarith