import Mathlib

theorem algebra_15071 {f : ℝ → ℝ} (hf : ∀ x > 0, f x > 0)
    (h : ∀ x y, x > y → y > 0 → f (x - y) = Real.sqrt (f (x * y) + 2)) :
    f 2009 = 2 := by

  have h1 : ∀ t > 0, f t = f 1 ^ 2 - 2 := by
    intro t ht
    have h11 : (1 + Real.sqrt (1 + 4 * t)) / 2 > 1 := by
      nlinarith [Real.sqrt_nonneg (1 + 4 * t), Real.sq_sqrt (show 1 + 4 * t ≥ 0 by linarith)]
    have h13 : ((1 + Real.sqrt (1 + 4 * t)) / 2 - 1 : ℝ) > 0 := by
      nlinarith [Real.sqrt_nonneg (1 + 4 * t), Real.sq_sqrt (show 1 + 4 * t ≥ 0 by linarith)]
    have h14 : f (((1 + Real.sqrt (1 + 4 * t)) / 2) - ((1 + Real.sqrt (1 + 4 * t)) / 2 - 1)) = Real.sqrt (f (((1 + Real.sqrt (1 + 4 * t)) / 2) * ((1 + Real.sqrt (1 + 4 * t)) / 2 - 1)) + 2) := by
      apply h
      all_goals
      all_goals
        try nlinarith [Real.sqrt_nonneg (1 + 4 * t), Real.sq_sqrt (show 1 + 4 * t ≥ 0 by linarith)]
    have h15 : ((1 + Real.sqrt (1 + 4 * t)) / 2) - ((1 + Real.sqrt (1 + 4 * t)) / 2 - 1) = (1 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (1 + 4 * t)]
    rw [h15] at h14
    have h16 : ((1 + Real.sqrt (1 + 4 * t)) / 2 : ℝ) * ((1 + Real.sqrt (1 + 4 * t)) / 2 - 1 : ℝ) = (t : ℝ) := by
      nlinarith [Real.sqrt_nonneg (1 + 4 * t), Real.sq_sqrt (show 1 + 4 * t ≥ 0 by linarith)]
    rw [h16] at h14
    have h17 : f 1 = Real.sqrt (f t + 2) := by
      linarith
    have h18 : f 1 ^ 2 = (Real.sqrt (f t + 2)) ^ 2 := by
      rw [h17]
    have h19 : (Real.sqrt (f t + 2)) ^ 2 = f t + 2 := by
      have ht20 : f t + 2 ≥ 0 := by
        have ht4 : f t > 0 := hf t (by linarith)
        linarith
      rw [Real.sq_sqrt (show f t + 2 ≥ 0 by linarith)]
    nlinarith [hf 1 (show 0 < (1 : ℝ) by norm_num), hf t (show 0 < (t : ℝ) by linarith)]

  have h10 : f 1 = f 1 ^ 2 - 2 := by
    specialize h1 1 (by norm_num)
    norm_num at h1 ⊢
    linarith
  have h110 : f 1 ^ 2 - f 1 - 2 = 0 := by
    nlinarith
  have h111 : (f 1 - 2) * (f 1 + 1) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h111) with h112 h113
  · -- solve the equation with $f 1 - 2 = 0$
    have h114 : f 1 = 2 := by linarith
    have h2 : ∀ t > 0, f t = 2 := by
      intro t ht
      have h3 : f t = f 1 ^ 2 - 2 := h1 t ht
      rw [show f 1 = (2 : ℝ) by linarith [h114]] at h3
      nlinarith
    have h3 : f 2009 = 2 := by
      apply h2 2009
      all_goals norm_num
    linarith
  · -- consider with $f 1 + 1 = 0$: contradicts with f 1 > 0
    have h1130 : f 1 < 0 := by linarith
    linarith [show f 1 ≥ 0 from by linarith [hf 1 (show 0 < (1 : ℝ) by norm_num)]]