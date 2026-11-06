import Mathlib

theorem algebra_144640 (x y : ℝ) (h₀ : y + Real.sqrt (y - 3 * x) + 3 * x = 12) (h₁ : y^2 + y - 3 * x - 9 * x^2 = 144) :
    (x = -24 ∧ y = 72) ∨ (x = -4 / 3 ∧ y = 12) := by
  have h2 : y - 3 * x ≥ 0 := by
    by_contra h
    push_neg at h
    have h3 : Real.sqrt (y - 3 * x) = 0 := by
      rw [Real.sqrt_eq_zero']
      all_goals linarith
    rw [h3] at h₀
    nlinarith
  set t := Real.sqrt (y - 3 * x) with ht
  have ht2 : t ≥ 0 := by positivity
  have eq1 : t^2 = y - 3 * x := by
    rw [ht]
    rw [Real.sq_sqrt]
    linarith
  have eq2 : 6 * x + t^2 + t = 12 := by
    have eq_y : y = 3 * x + t^2 := by linarith [eq1]
    rw [eq_y] at h₀
    have eq_t0 : t = Real.sqrt (y - 3 * x) := by linarith [ht]
    rw [eq_t0] at h₀
    nlinarith [Real.sq_sqrt (show y - 3 * x ≥ 0 by linarith)]
  have eq3 : 6 * x * t^2 + t^4 + t^2 = 144 := by
    have eq6 : y = 3 * x + t^2 := by linarith [eq1]
    rw [eq6] at h₁
    nlinarith [sq_nonneg (x + 24), sq_nonneg (y - 72), sq_nonneg (t^2 - 144), sq_nonneg (t - 12), sq_nonneg (t + 3), sq_nonneg (t - 4)]
  have eq4 : (12 - t^2 - t) * t^2 + t^4 + t^2 = 144 := by
    have eq7 : 6 * x = 12 - t^2 - t := by
      linarith
    rw [show 6 * x = 12 - t^2 - t by linarith] at eq3
    nlinarith
  have eq5 : t^3 - 13 * t^2 + 144 = 0 := by
    nlinarith
  have eq6 : (t - 4) * (t - 12) * (t + 3) = 0 := by 
    nlinarith [sq_nonneg (t - 4), sq_nonneg (t - 12), sq_nonneg (t + 3)]
  cases' (mul_eq_zero.mp eq6) with eq7 eq8
  · cases' (mul_eq_zero.mp eq7) with eq8 eq9
    · -- Case t - 4 = 0, i.e., t = 4
      have ht4 : t = 4 := by linarith
      have hx : x = -4 / 3 := by
        nlinarith [eq2, ht4, sq_nonneg (t), eq1]
      have hy : y = 12 := by
        nlinarith [hx, eq1, ht4]
      right
      exact ⟨hx, hy⟩
    · -- Case t - 12 = 0, i.e., t = 12
      have ht12 : t = 12 := by linarith
      have hx : x = -24 := by
        nlinarith [eq2, ht12, sq_nonneg (t), eq1]
      have hy : y = 72 := by
        nlinarith [hx, eq1, ht12]
      left
      exact ⟨hx, hy⟩
  · -- Case t + 3 = 0, i.e., t = -3, which is a contradiction
    have ht3 : t = -3 := by linarith
    nlinarith [show t ≥ 0 from ht2, sq_nonneg (t), eq1, sq_nonneg (t + 3)]