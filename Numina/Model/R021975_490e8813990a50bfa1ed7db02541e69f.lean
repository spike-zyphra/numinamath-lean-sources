import Mathlib

theorem algebra_322050 {p : ℝ} (f : ℝ → ℝ) (hf : f = fun x => x^2 - 2 * p * x - p)
    (A B : ℝ) (hA : f A = 0) (hB : f B = 0) (hAB : A ≠ B) :
    2 * p * A + B^2 + 3 * p > 0 ∧ (|A - B| ≤ |2 * p - 3| → p ≤ 3 / 2) := by
  have h1 : A^2 - 2 * p * A - p = 0 := by
    rw [hf] at hA
    simp at hA
    linarith
  have h2 : B^2 - 2 * p * B - p = 0 := by
    rw [hf] at hB
    simp at hB
    linarith
  have h3 : A + B = 2 * p := by
    have h4 : A^2 - 2 * p * A - p = 0 := h1
    have h5 : B^2 - 2 * p * B - p = 0 := h2
    have h6 : A^2 - B^2 = 2 * p * (A - B) := by
      nlinarith
    have h7 : A - B ≠ 0 := by
      intro h
      apply hAB
      linarith
    have h8 : (A + B : ℝ) = 2 * p := by
      have h9 : (A - B : ℝ) * (A + B - 2 * p) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h9) with h10 h11
      · -- $A - B = 0$, which contradicts $A ≠ B$.
        exfalso
        apply hAB
        linarith
      · -- $A + B - 2p = 0$, which means $A + B = 2p$.
        linarith
    linarith
  have h4 : B^2 = 2 * p * B + p := by
    linarith
  have h5 : 2 * p * A + B^2 + 3 * p = 4 * (p ^ 2 + p) := by
    nlinarith [h4, h3]
  have h6 : 4 * (p ^ 2 + p) > 0 := by
    have h7 : (A - B) ^ 2 > 0 := by
      apply pow_two_pos_of_ne_zero
      intro h
      apply hAB
      linarith
    nlinarith [sq_nonneg (A - B), sq_nonneg (A + B - 2 * p), sq_pos_of_pos (show 0 < (1 : ℝ) by linarith)]
  have h7 : 2 * p * A + B^2 + 3 * p > 0 := by
    linarith [h5, h6]
  constructor
  · linarith
  · -- Proof of (2)
    intro h
    have h8 : (A - B) ^ 2 ≤ (2 * p - 3) ^ 2 := by
      apply sq_le_sq.mpr
      simpa using h
    have h10 : (A - B) ^ 2 > 0 := by
      apply pow_two_pos_of_ne_zero
      intro h
      apply hAB
      linarith
    nlinarith [sq_nonneg (A - B), sq_nonneg (A - B), sq_nonneg (2 * p - 3), sq_nonneg (A + B - 2 * p), sq_pos_of_pos (show (0 : ℝ) < 2 by linarith)]