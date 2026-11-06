import Mathlib

theorem algebra_242846 {k : ℝ} (h : ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ 2*x1^2+k*x1-2*k+1=0 ∧ 2*x2^2+k*x2-2*k+1=0 ∧ x1^2+x2^2=29/4) :
    k=3 := by
  obtain ⟨x1, x2, hxne, h1, h2, h3⟩ := h
  have h4 : (x1 - x2) * (2 * (x1 + x2) + k) = 0 := by
    nlinarith
  have h5 : 2 * (x1 + x2) + k = 0 := by
    apply_fun (fun y => y / (x1 - x2)) at h4
    field_simp [sub_ne_zero.2 hxne] at h4
    linarith
  have h6 : x1 + x2 = -k / 2 := by linarith
  have h7 : k ^ 2 + 8 * k - 33 = 0 := by
    nlinarith [h6, h1, h2, h3, sq_pos_of_ne_zero (sub_ne_zero.2 hxne)]
  have h8 : (k - 3) * (k + 11) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h8) with hk1 hk2
  · -- k - 3 = 0, hence k = 3
    linarith
  · -- k + 11 = 0, hence k = -11
    have h9 : k = -11 := by linarith
    -- Verify the discriminant for k = -11, must be non-negative by real roots
    -- At k = -11: trace to get discriminant contradiction
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.2 hxne), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2), sq_nonneg (k), h9]