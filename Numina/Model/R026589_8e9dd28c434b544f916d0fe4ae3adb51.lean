import Mathlib

theorem inequalities_207079 (x : ℝ) (hx : x > 0) :
    11 / (x + 1.5) + 8 / x ≥ 12 / (x + 2) + 2 ↔ (x - 4) * (x + 1) * (x + 3) ≤ 0 := by
  constructor
  · -- Forward implication: assuming the inequality, proving the polynomial is ≤ 0
    intro h
    have hx1 : x + 1.5 > 0 := by
      nlinarith
    have hx2 : x + 2 > 0 := by
      nlinarith
    have h1 : (11 / (x + 1.5) + 8 / x) - (12 / (x + 2) + 2) ≥ 0 := by linarith
    have h2 : (11 * x * (x + 2) + 8 * (x + 1.5) * (x + 2) - (12 * x * (x + 1.5) + 2 * x * (x + 1.5) * (x + 2))) / (x * (x + 1.5) * (x + 2)) ≥ 0 := by
      have h3 : (11 / (x + 1.5) + 8 / x) - (12 / (x + 2) + 2) = 
        (11 * x * (x + 2) + 8 * (x + 1.5) * (x + 2) - (12 * x * (x + 1.5) + 2 * x * (x + 1.5) * (x + 2))) / (x * (x + 1.5) * (x + 2)) := by 
        field_simp
        <;> ring
      linarith [h3, h1]
    have h3 : 11 * x * (x + 2) + 8 * (x + 1.5) * (x + 2) - (12 * x * (x + 1.5) + 2 * x * (x + 1.5) * (x + 2)) ≥ 0 := by
      have pos1 : x * (x + 1.5) * (x + 2) > 0 := by positivity
      apply (div_nonneg_iff).mp at h2
      cases h2 with
      | inl h2l =>
        nlinarith
      | inr h2r =>
        nlinarith
    have h4 : (x - 4) * (x + 1) * (x + 3) ≤ 0 := by
      ring_nf at h3
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg ((x + 2) ^ 2), sq_nonneg ((x + 1) ^ 2), sq_nonneg ((x + 3) ^ 2), mul_pos hx (show 0 < x + 1.5 by nlinarith), mul_pos hx (show 0 < x + 2 by nlinarith)]
    linarith
  · -- Backward implication: assuming the polynomial is ≤ 0, proving the inequality
    intro h
    have hx1 : x + 1.5 > 0 := by
      nlinarith
    have hx2 : x + 2 > 0 := by
      nlinarith
    have h4 : (x - 4) * (x + 1) * (x + 3) ≤ 0 := by linarith
    have h3 : 11 * x * (x + 2) + 8 * (x + 1.5) * (x + 2) ≥ 12 * x * (x + 1.5) + 2 * x * (x + 1.5) * (x + 2) := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg ((x + 2) ^ 2), sq_nonneg ((x + 1) ^ 2), sq_nonneg ((x + 3) ^ 2), mul_pos hx (show 0 < x + 1.5 by nlinarith), mul_pos hx (show 0 < x + 2 by nlinarith)]
    have h2 : (11 / (x + 1.5) + 8 / x) ≥ (12 / (x + 2) + 2) := by
      have pos1 : x * (x + 1.5) * (x + 2) > 0 := by positivity
      have h6 : (11 * x * (x + 2) + 8 * (x + 1.5) * (x + 2) - (12 * x * (x + 1.5) + 2 * x * (x + 1.5) * (x + 2))) ≥ 0 := by linarith
      have h5 : (11 / (x + 1.5) + 8 / x) - (12 / (x + 2) + 2) ≥ 0 := by
        have h7 : (11 / (x + 1.5) + 8 / x) - (12 / (x + 2) + 2) = 
          (11 * x * (x + 2) + 8 * (x + 1.5) * (x + 2) - (12 * x * (x + 1.5) + 2 * x * (x + 1.5) * (x + 2))) / (x * (x + 1.5) * (x + 2)) := by 
          field_simp
          <;> ring
        rw [h7] at *
        apply div_nonneg
        linarith
        positivity
      linarith
    linarith