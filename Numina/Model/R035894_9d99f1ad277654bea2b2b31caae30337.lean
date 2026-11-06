import Mathlib

theorem algebra_1549 {a : ℝ} (ha : ∃ x1 x2, x1 ≠ x2 ∧ 2*x1^2+a*x1-2*a+1=0 ∧ 2*x2^2+a*x2-2*a+1=0 ∧ x1^2+x2^2=7+1/4) :
    a=3 := by
  rcases ha with ⟨x1, x2, h12, h1, h2, h3⟩
  have h4 : x1^2 + x2^2 = 29 / 4 := by
    norm_num at h3 ⊢
    linarith
  have eq1 : 2 * (x1^2 - x2^2) + a * (x1 - x2) = 0 := by
    linarith
  have h5 : x1 - x2 ≠ 0 := by
    intro h
    apply h12
    linarith
  have eq2 : 2 * (x1 + x2) + a = 0 := by
    apply (mul_left_inj' h5).mp
    linarith
  have eq3 : 2 * (x1^2 + x2^2) + a * (x1 + x2) - 4 * a + 2 = 0 := by
    nlinarith
  rw [show x1^2 + x2^2 = 29 / 4 by linarith] at eq3
  have eq4 : x1 + x2 = -a / 2 := by
    nlinarith
  rw [show x1 + x2 = -a / 2 by linarith] at eq3
  have h5 : a ^ 2 + 8 * a - 33 = 0 := by
    nlinarith
  have h6 : (a - 3) * (a + 11) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h6) with h7 h8
  · -- a = 3
    linarith
  · -- a = -11
    have h7 : a = -11 := by linarith
    rw [h7] at h1 h2
    nlinarith [sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by
      intro h
      apply h12
      linarith
    ), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2), sq_nonneg (2 * x1 - 2 * x2)]