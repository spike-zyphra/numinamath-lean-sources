import Mathlib

theorem algebra_186954 (x : ℝ) (hx : x > 0) (h : 2 * (x ^ ((1 : ℝ) / 3)) + 5 * (x ^ ((1 : ℝ) / 6)) - 18 = 0) :
    x = 64 := by
  have h1 : (x ^ ((1 : ℝ) / 3)) = (x ^ ((1 : ℝ) / 6)) ^ 2 := by
    have h2 : (x ^ ((1 : ℝ) / 6)) ^ 2 = x ^ ((1 / 3 : ℝ)) := by
      have h3 : (x ^ ((1 : ℝ) / 6)) ^ 2 = x ^ (2 * (1 / 6 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        ring_nf
        all_goals positivity
      have h4 : 2 * (1 / 6 : ℝ) = (1 / 3 : ℝ) := by norm_num
      rw [h4] at h3
      all_goals linarith
    linarith [h2]
  have eq1 : 2 * (x ^ ((1 : ℝ) / 6)) ^ 2 + 5 * (x ^ ((1 : ℝ) / 6)) - 18 = 0 := by
    rw [h1] at h
    linarith [h]
  have cases : ((x ^ ((1 : ℝ) / 6)) - 2) * ((x ^ ((1 : ℝ) / 6)) + (9 / 2)) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp cases) with h3 h4
  · -- Let $t = x^{1/6}$, then the equation becomes $2t^2 + 5t - 18 = 0$. Solving gives $t = 2$ or $t = -9/2$. Since $t > 0$, so $t = 2$, and $x = t^6 = 64$.
    have h5 : x ^ ((1 : ℝ) / 6) = 2 := by linarith
    have h6 : x = (2 : ℝ) ^ 6 := by
      have h7 : x ^ ((1 : ℝ) / 6) = (2 : ℝ) := by linarith [h5]
      have h8 : (x ^ ((1 : ℝ) / 6 : ℝ)) ^ 6 = (2 : ℝ) ^ 6 := by
        rw [h7]
      have h9 : (x ^ ((1 : ℝ) / 6 : ℝ)) ^ 6 = x := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals positivity
      rw [h9] at h8
      linarith
    norm_num at h6 ⊢
    all_goals linarith
  · -- Second case leads to contradiction since $x > 0$.
    have h7 : x ^ ((1 : ℝ) / 6) = (-9 / 2 : ℝ) := by
      nlinarith
    have h8 : x ^ ((1 : ℝ) / 6) > 0 := by positivity
    nlinarith [h7, h8]