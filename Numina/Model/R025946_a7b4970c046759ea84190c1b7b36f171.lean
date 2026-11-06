import Mathlib

theorem algebra_215866 (m : ℝ) (a b : ℝ × ℝ)
    (ha : a = (2 ^ m, -1)) (hb : b = (2 ^ m - 1, 2 ^ (m + 1)))
    (hperp : a.1 * b.1 + a.2 * b.2 = 0) :
    Real.sqrt (a.1 ^ 2 + a.2 ^ 2) = Real.sqrt 10 := by
  rw [ha] at hperp
  rw [hb] at hperp
  have h1 : (2 : ℝ) ^ m * ((2 : ℝ) ^ m - 1) + (-1) * ((2 : ℝ) ^ (m + 1)) = 0 := by
    simp [Prod.fst, Prod.snd] at hperp ⊢
    linarith
  have h2 : (2 : ℝ) ^ (m + 1) = 2 * (2 : ℝ) ^ m := by
    rw [Real.rpow_add]
    ring_nf
    all_goals linarith
  rw [h2] at h1
  have h3 : (2 : ℝ) ^ m * ((2 : ℝ) ^ m - 1) - 2 * (2 : ℝ) ^ m = 0 := by
    nlinarith
  have h4 : (2 : ℝ) ^ m * ((2 : ℝ) ^ m - 3) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- Show that $2^m > 0$ for all real m, so $2^m = 0$ is impossible
    have h7 : (2 : ℝ) ^ m > 0 := by positivity
    linarith
  · -- Case where 2^m - 3 = 0, so 2^m = 3
    have h8 : (2 : ℝ) ^ m = 3 := by linarith
    -- Goal is Real.sqrt (a.1 ^ 2 + a.2 ^ 2) = Real.sqrt 10
    rw [ha]
    simp only [Prod.fst, Prod.snd]
    rw [h8]
    all_goals norm_num