import Mathlib

open Real

theorem algebra_95017 {a b : ℝ} (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b ∧ b ≠ 1) :
    logb a b * logb b a = 1 := by
  have h1 : logb a b = log b / log a := by 
    field_simp [logb]
  have h2 : logb b a = log a / log b := by 
    field_simp [logb]
  rw [h1, h2]
  have h3 : log a ≠ 0 := by
    have h4 : 0 < a := ha.1
    have h5 : a ≠ 1 := ha.2
    have h6 : log a ≠ 0 := by
      have h7 : a > (0 : ℝ) := by linarith [h4]
      by_contra h
      have h8 : a = 1 := by
        have h9 : log a = 0 := by assumption
        rw [Real.log_eq_zero] at h9
        rcases h9 with (r | r | r)
        · linarith
        · linarith
        · linarith [show 0 < a from h4]
      contradiction
    exact h6
  have h8 : log b ≠ 0 := by
    have h9 : 0 < b := hb.1
    have h10 : b ≠ 1 := hb.2
    have h11 : log b ≠ 0 := by
      have h7 : b > (0 : ℝ) := by linarith [h9]
      by_contra h
      have h12 : b = 1 := by
        have h13 : log b = 0 := by assumption
        rw [Real.log_eq_zero] at h13
        rcases h13 with (r | r | r)
        · linarith
        · linarith
        · linarith [show 0 < b from hb.1]
      contradiction
    exact h11
  field_simp [h3, h8]
  all_goals linarith