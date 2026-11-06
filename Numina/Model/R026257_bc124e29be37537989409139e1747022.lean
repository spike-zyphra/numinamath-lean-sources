import Mathlib

theorem inequalities_598241 (a b p q : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hp : 1 < p) (hq : 1 < q) (hroots : 1 / p + 1 / q = 1) :
    a * b ≤ 1 / p * a ^ p + 1 / q * b ^ q := by

  have h1 : 0 < p := by linarith
  have h2 : 0 < q := by linarith
  have hp2 : p > 1 := by linarith
  have hq2 : q > 1 := by linarith
  have h3 : a ^ p ≥ 0 := by positivity
  have h4 : b ^ q ≥ 0 := by positivity
  have h5 : 1 / p ≥ 0 := by
    apply div_nonneg
    norm_num
    linarith
  have h6 : 1 / q ≥ 0 := by
    apply div_nonneg
    norm_num
    linarith
  have h7 : 1 / p + 1 / q = 1 := hroots
  have h8 : (a ^ p : ℝ) ^ (1 / p : ℝ) * (b ^ q : ℝ) ^ (1 / q : ℝ) ≤ 1 / p * (a ^ p : ℝ) + 1 / q * (b ^ q : ℝ) := by
    apply Real.geom_mean_le_arith_mean2_weighted
    all_goals
      try positivity
      try linarith
  have h9 : (a ^ p : ℝ) ^ (1 / p : ℝ) = a := by
    rw [← Real.rpow_mul]
    field_simp
    all_goals
      nlinarith
  have h10 : (b ^ q : ℝ) ^ (1 / q : ℝ) = b := by
    rw [← Real.rpow_mul]
    field_simp
    all_goals
      nlinarith
  have h11 : (a ^ p : ℝ) ^ (1 / p : ℝ) * (b ^ q : ℝ) ^ (1 / q : ℝ) = a * b := by
    rw [h9, h10]
  linarith [h11, h8]