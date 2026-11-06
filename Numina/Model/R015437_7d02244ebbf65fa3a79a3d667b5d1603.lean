import Mathlib

open Set Real

theorem inequalities_12763 {x : ℝ} (hx : (x - 1) * (x - 3) * (x - 5) < 0) :
    (x - 2) * (x - 4) * (x - 6) > 0 ↔ 3 < x ∧ x < 4 := by
  constructor
  · -- Assume (x - 2) * (x - 4) * (x - 6) > 0
    intro h
    have h3 : 3 < x := by
      by_contra h5
      push_neg at h5
      have h5 : x ≤ 3 := by linarith
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 3), sq_nonneg (x - 5), sq_nonneg (x - 2), sq_nonneg (x - 4), sq_nonneg (x - 6)]
    have h4 : x < 4 := by
      by_contra h6
      push_neg at h6
      have h6 : x ≥ 4 := by linarith
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 3), sq_nonneg (x - 5), sq_nonneg (x - 2), sq_nonneg (x - 4), sq_nonneg (x - 6)]
    constructor <;> linarith
  · -- Now proving the reverse
    rintro ⟨h1, h2⟩
    have h4 : (x - 2) * (x - 4) * (x - 6) > 0 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 3), sq_nonneg (x - 5), sq_nonneg (x - 2), sq_nonneg (x - 4), sq_nonneg (x - 6)]
    assumption