import Mathlib

theorem algebra_289524 {s t : ℝ} (hs : 19 * s^2 + 99 * s + 1 = 0) (ht : t^2 + 99 * t + 19 = 0)
    (hst : s * t ≠ 1) : (s * t + 4 * s + 1) / t = -5 := by
  have h1 : t ≠ 0 := by
    by_contra h
    have ht0 : t = 0 := by linarith
    rw [ht0] at ht
    nlinarith
  -- Show that (s * t - 1) * (19 * s - t) = 0
  have eq1 : (s * t - 1) * (19 * s - t) = 0 := by
    have eq2 : 19 * s^2 * t + 99 * s * t + t = 0 := by
      have eq3 : 19 * s^2 + 99 * s + 1 = 0 := hs
      have eq3' : (19 * s^2 + 99 * s + 1) * t = 0 := by
        rw [eq3]
        all_goals
          ring_nf
          <;> nlinarith
      have eq4 : t ≠ 0 := h1
      nlinarith
    have eq3 : t^2 * s + 99 * t * s + 19 * s = 0 := by
      have eq5 : t^2 + 99 * t + 19 = 0 := ht
      have eq6 : (t^2 + 99 * t + 19) * s = 0 := by
        rw [eq5]
        all_goals
          ring_nf
          <;> nlinarith
      have eq7 : t^2 * s + 99 * t * s + 19 * s = 0 := by
        linarith [eq6]
      linarith [eq7]
    nlinarith [sq_pos_of_ne_zero (show t ≠ 0 by assumption), sq_nonneg (s * t - 1)]
  cases' (mul_eq_zero.mp eq1) with h2 h3
  · -- h2 : s * t - 1 = 0
    exfalso
    apply hst
    linarith
  · -- h3 : 19 * s - t = 0 
    have ht19s : t = 19 * s := by linarith
    have eq4 : t = 19 * s := ht19s
    have h4 : s * t + 4 * s + 1 = -95 * s := by
      rw [show t = 19 * s by linarith [eq4]]
      nlinarith [hs, sq_nonneg (s)]
    have h5 : (s * t + 4 * s + 1) / t = -5 := by
      rw [show (s * t + 4 * s + 1) = -95 * s by linarith [h4]]
      rw [show t = 19 * s by linarith [eq4]]
      have h6 : s ≠ 0 := by
        by_contra h
        have hs0 : s = 0 := by linarith
        rw [hs0] at hs
        nlinarith
      have h7 : 19 * s ≠ 0 := by
        intro h8
        apply h6
        linarith
      field_simp [h7]
      <;> nlinarith
    exact h5