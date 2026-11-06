import Mathlib

theorem inequalities_90296 (a b c : ℝ) (ha : a ≠ b) (hc : 0 < c)
    (h1 : a ^ 4 - 2019 * a = c) (h2 : b ^ 4 - 2019 * b = c) :
    -Real.sqrt c < a * b ∧ a * b < 0 := by 
  have eq1 : a ^ 4 - b ^ 4 = 2019 * (a - b) := by
    nlinarith
  have eq2 : a^4 - b^4 = (a^2 - b^2) * (a^2 + b^2) := by
    ring
  rw [eq2] at eq1
  have eq3 : a^2 - b^2 = (a - b) * (a + b) := by
    ring
  rw [eq3] at eq1
  -- Now, `eq1` is (a - b) * (a + b) * (a^2 + b^2) = 2019 * (a - b).
  have h3 : (a - b) ≠ 0 := by
    intro h
    apply ha
    linarith [h]
  have h4 : (a + b) * (a^2 + b^2) = 2019 := by
    apply (mul_left_inj' h3).mp
    linarith [eq1]
  have eq5 : a * b < 0 := by
    by_contra h
    push_neg at h
    have h6 : a * b ≥ 0 := by linarith
    nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a * b), sq_nonneg (a + b), sq_nonneg (a - b), sq_pos_of_pos hc, sq_pos_of_ne_zero (show (a - b) ≠ 0 by exact h3), sq_nonneg (a^2 - b^2), sq_nonneg (a^2 * b^2)]
  have eq6 : -Real.sqrt c < a * b := by
    have h5 : (a * b) ^ 2 < c := by
      nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a * b), sq_nonneg (a + b), sq_nonneg (a - b), h4, sq_nonneg (a^2 - b^2), sq_nonneg (a^2 * b^2)]
    have h6 : (a * b) ^ 2 < c := h5
    have h7 : Real.sqrt c ^ 2 > (a * b) ^ 2 := by
      have h11 : Real.sqrt c ^ 2 = c := by
        rw [Real.sq_sqrt]
        linarith
      nlinarith [h6, h11, Real.sqrt_nonneg c, sq_nonneg (a * b)]
    have h6_neg : a * b < 0 := by linarith [eq5]
    have h8 : -Real.sqrt c < a * b := by
      nlinarith [Real.sqrt_nonneg c, Real.sq_sqrt (show 0 ≤ c by linarith), sq_nonneg (a * b), h7]
    linarith [h8]
  constructor
  · linarith [eq6]
  · linarith [eq5]