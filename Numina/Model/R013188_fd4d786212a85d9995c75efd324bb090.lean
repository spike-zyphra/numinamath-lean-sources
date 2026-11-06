import Mathlib

open Real

theorem inequalities_114049 {a b : ℝ} (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b ∧ b ≠ 1) :
    logb a b ^ 2 + logb b a ^ 2 ≥ logb a b + logb b a := by
  have h1 : 0 < a := ha.1
  have ha2 : a ≠ 1 := ha.2
  have h2 : 0 < b := hb.1
  have hb2 : b ≠ 1 := hb.2
  have h3 : log a ≠ 0 := by
    by_contra h
    have : a = 1 := by
      rw [Real.log_eq_zero] at h
      rcases h with (r | r | r)
      · linarith
      · linarith
      · linarith
    tauto
  have h4 : log b ≠ 0 := by
    by_contra h
    have : b = 1 := by
      rw [Real.log_eq_zero] at h
      rcases h with (r | r | r)
      · linarith
      · linarith
      · linarith
    tauto
  have h5 : logb a b = log b / log a := by
    field_simp [Real.logb]
  have h6 : logb b a = log a / log b := by
    field_simp [Real.logb]
  have h7 : logb a b * logb b a = 1 := by
    rw [h5, h6]
    field_simp [h3, h4]
  nlinarith [sq_nonneg (logb a b - 1), sq_nonneg (logb b a - 1),
          sq_nonneg (logb a b * logb b a - 1), h7, 
          sq_nonneg (logb a b - logb b a)
        ]