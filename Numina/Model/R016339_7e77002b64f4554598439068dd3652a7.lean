import Mathlib

theorem algebra_318165 (m : ℤ) (h : ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ 3*x1^2+m*x1-2=0 ∧ 3*x2^2+m*x2-2=0 ∧
    x1 > -9/5 ∧ x1 < 3/7 ∧ x2 > -9/5 ∧ x2 < 3/7) : m = 4 := by
  rcases h with ⟨x1, x2, hx12, h1, h2, hx11, hx1, hx21, hx2⟩
  have h3 : (x1 - x2) * (3 * (x1 + x2) + (m : ℝ)) = 0 := by
    nlinarith
  cases (mul_eq_zero.mp h3) with
  | inl h4 =>
    exfalso
    have h44 : x1 = x2 := by linarith
    contradiction
  | inr h5 =>
    have h4 : (x1 + x2 : ℝ) = (- (m : ℝ) / 3) := by
      linarith
    have h5 : (x1 * x2 : ℝ) = (-2 / 3 : ℝ) := by
      nlinarith [sq_pos_of_ne_zero (show (x1 - x2 : ℝ) ≠ 0 by
        intro h0
        apply hx12
        linarith
      ), h4]
    have h6 : m ≥ -2 := by
      by_contra h
      push_neg at h
      have h7 : (m : ℝ) < (-2 : ℝ) := by exact_mod_cast h
      nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 + 9/5), sq_nonneg (x2 + 9/5), sq_nonneg (x1 - 3/7), sq_nonneg (x2 - 3/7)]
    have h7 : m ≤ 10 := by
      by_contra h
      push_neg at h
      have h8 : (m : ℝ) > (10 : ℝ) := by exact_mod_cast h
      nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 + 9/5), sq_nonneg (x2 + 9/5), sq_nonneg (x1 - 3/7), sq_nonneg (x2 - 3/7)]
    interval_cases m <;> norm_num at h4 h5 ⊢
    <;> nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 + 9/5), sq_nonneg (x2 + 9/5), sq_nonneg (x1 - 3/7), sq_nonneg (x2 - 3/7)]