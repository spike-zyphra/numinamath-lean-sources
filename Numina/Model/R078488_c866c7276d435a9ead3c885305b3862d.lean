import Mathlib

theorem algebra_12055 (m : ℝ) (a b : ℝ × ℝ)
    (ha : a.1 = 2 ^ m ∧ a.2 = -1)
    (hb : b.1 = 2 ^ m - 1 ∧ b.2 = 2 ^ (m + 1))
    (hperp : a.1 * b.1 + a.2 * b.2 = 0) :
    Real.sqrt (a.1 ^ 2 + a.2 ^ 2) = Real.sqrt 10 := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rw [ha1, ha2, hb1, hb2] at hperp
  have eq1 : (2 : ℝ) ^ m * (2 ^ m - 1) + (-1) * (2 ^ (m + 1 : ℝ)) = 0 := by
    simpa using hperp
  have h1 : (2 : ℝ) ^ (m + 1 : ℝ) = (2 : ℝ) ^ m * 2 := by
    rw [Real.rpow_add]
    simp
    all_goals linarith
  have eq2 : (2 : ℝ) ^ m * (2 ^ m - 1) + (-1) * (2 ^ (m + 1 : ℝ)) = (2 : ℝ) ^ (2 * m) - 3 * (2 : ℝ) ^ m := by
    rw [h1]
    have h2 : (2 : ℝ) ^ (2 * m) = ((2 : ℝ) ^ m) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      ring_nf
      all_goals linarith
    rw [h2]
    ring_nf
  have eq3 : (2 : ℝ) ^ (2 * m) - 3 * (2 : ℝ) ^ m = 0 := by
    linarith [eq1, eq2]
  have h_eq2 : ((2 : ℝ) ^ m) * ((2 : ℝ) ^ m - 3) = 0 := by
    have h1 : (2 : ℝ) ^ (2 * m) - 3 * (2 : ℝ) ^ m = 0 := by
      linarith [eq3]
    have h2 : (2 : ℝ) ^ (2 * m) = ((2 : ℝ) ^ m) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      ring_nf
      all_goals linarith
    rw [h2] at h1
    nlinarith
  cases' (mul_eq_zero.1 h_eq2) with h5 h6
  · -- Show contradiction in case $2^m = 0$
    have h6 : (2 : ℝ) ^ m > 0 := by
      positivity
    linarith
  · -- Solve case $2^m - 3 = 0$, so $2^m = 3$
    have h_eq3 : (2 : ℝ) ^ m = 3 := by linarith
    rw [ha1, ha2]
    rw [h_eq3]
    norm_num