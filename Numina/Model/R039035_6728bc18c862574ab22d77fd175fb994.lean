import Mathlib

theorem algebra_309 {a b : ℝ} (ha : a ≠ b) (hb : b ≠ -a) :
    1 / (a - b) + 1 / (a + b) + 2 * a / (a ^ 2 + b ^ 2) +
    4 * a ^ 3 / (a ^ 4 + b ^ 4) = 8 * a ^ 7 / (a ^ 8 - b ^ 8) := by
  have h1 : a - b ≠ 0 := by
    intro h
    apply ha
    linarith
  have h2 : a + b ≠ 0 := by
    intro h
    have h3 : b = -a := by linarith
    contradiction
  have h3 : a ^ 2 + b ^ 2 ≠ 0 := by
    by_contra h
    have h4 : a ^ 2 ≥ 0 := sq_nonneg a
    have h5 : b ^ 2 ≥ 0 := sq_nonneg b
    have h6 : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have h7 : a = 0 := pow_eq_zero h6
    have h8 : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have h9 : b = 0 := pow_eq_zero h8
    have h10 : a - b = 0 := by linarith
    contradiction
  have h4 : a ^ 4 + b ^ 4 ≠ 0 := by
    by_contra h
    have h4 : a ^ 4 ≥ 0 := by positivity
    have h5 : b ^ 4 ≥ 0 := by positivity
    have h6 : a ^ 4 = 0 := by nlinarith [sq_nonneg (a ^ 2), sq_nonneg (b ^ 2)]
    have h7 : a ^ 2 = 0 := by
      have h8 : a ^ 4 = (a ^ 2) ^ 2 := by ring
      rw [h8] at h6
      have h9 : a ^ 2 = 0 := by nlinarith [sq_nonneg (a ^ 2)]
      assumption
    have h8 : a = 0 := by
      have h9 : a ^ 2 = 0 := h7
      have h10 : a = 0 := by nlinarith [sq_nonneg a]
      assumption
    have h9 : b ^ 4 = 0 := by nlinarith [sq_nonneg (a ^ 2), sq_nonneg (b ^ 2)]
    have h10 : b ^ 2 = 0 := by
      have h11 : b ^ 4 = (b ^ 2) ^ 2 := by ring
      rw [h11] at h9
      have h12 : b ^ 2 = 0 := by nlinarith [sq_nonneg (b ^ 2)]
      assumption
    have h11 : b = 0 := by
      have h12 : b ^ 2 = 0 := h10
      have h13 : b = 0 := by nlinarith [sq_nonneg b]
      assumption
    have h12 : a - b = 0 := by linarith
    contradiction
  have h5 : a ^ 8 - b ^ 8 ≠ 0 := by
    by_contra h
    have h6 : a ^ 8 = b ^ 8 := by linarith
    have h7 : a ^ 4 = b ^ 4 ∨ a ^ 4 = -b ^ 4 := by
      have h8 : (a ^ 4) ^ 2 = (b ^ 4) ^ 2 := by nlinarith
      have h9 : a ^ 4 = b ^ 4 ∨ a ^ 4 = -b ^ 4 := by
        apply sq_eq_sq_iff_eq_or_eq_neg.mp
        linarith
      assumption
    cases h7 with
    | inl h8 =>
      have h9 : a ^ 2 = b ^ 2 ∨ a ^ 2 = -b ^ 2 := by
        have h10 : (a ^ 2) ^ 2 = (b ^ 2) ^ 2 := by nlinarith
        apply sq_eq_sq_iff_eq_or_eq_neg.mp at h10
        assumption
      cases h9 with
      | inl h10 =>
        have h11 : a = b ∨ a = -b := by
          apply sq_eq_sq_iff_eq_or_eq_neg.mp
          linarith
        cases h11 with
        | inl h12 =>
          have h13 : a - b = 0 := by linarith
          contradiction
        | inr h12 =>
          have h14 : a + b = 0 := by linarith
          contradiction
      | inr h10 =>
        have h11 : a ^ 2 + b ^ 2 = 0 := by nlinarith
        contradiction
    | inr h8 =>
      have h10 : a ^ 4 + b ^ 4 = 0 := by nlinarith
      contradiction
  have h8 : a ^ 8 - b ^ 8 = (a - b) * (a + b) * (a ^ 2 + b ^ 2) * (a ^ 4 + b ^ 4) := by
    ring_nf
  rw [h8]
  field_simp [(show (a - b) ≠ 0 by assumption), (show (a + b) ≠ 0 by assumption),
    (show (a ^ 2 + b ^ 2) ≠ 0 by assumption), (show (a ^ 4 + b ^ 4) ≠ 0 by assumption)]
  ring_nf