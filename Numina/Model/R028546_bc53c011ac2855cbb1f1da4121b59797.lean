import Mathlib

theorem algebra_206724 (a b c : ℝ) (hc : c ≠ 1) (h1 : ∃ x, x^2 + a * x + 1 = 0 ∧ x^2 + b * x + c = 0)
    (h2 : ∃ x, x^2 + x + a = 0 ∧ x^2 + c * x + b = 0) : a + b + c = -3 := by
  rcases h1 with ⟨r, h11, h12⟩
  rcases h2 with ⟨s, h21, h22⟩
  have h_sub1 : r * (a - b) = (c - 1) := by nlinarith
  have h_sub2 : s * (c - 1) = (a - b) := by nlinarith
  have h_ne : a - b ≠ 0 := by
    by_contra h_eq
    have hc_eq_1 : c = 1 := by
      rw [h_eq] at h_sub1
      nlinarith
    contradiction
  have h_eq : (s * r) * (a - b) = (a - b) := by
    have h1 : (s * r) * (a - b) = s * (r * (a - b)) := by ring
    have h2 : r * (a - b) = (c - 1) := by
      linarith
    have h3 : s * (r * (a - b)) = s * (c - 1) := by
      rw [h2]
    have h4 : s * (c - 1) = (a - b) := by
      linarith
    rw [h4] at h3
    linarith
  have h_eq2 : s * r = 1 := by
    apply (mul_left_inj' h_ne).mp
    linarith
  have h_s_ne_0 : s ≠ 0 := by
    by_contra h_eq
    rw [h_eq] at h_eq2
    nlinarith
  have h_r_ne_0 : r ≠ 0 := by
    by_contra h_eq
    rw [h_eq] at h_eq2
    nlinarith
  have h_eq3 : a = -2 := by
    nlinarith [sq_nonneg (r - s), sq_nonneg (s - 1), sq_nonneg (r - 1), sq_pos_of_ne_zero (show (c - 1 : ℝ) ≠ 0 by
      by_contra h_eq
      have hc_eq_1 : c = 1 := by
        nlinarith
      contradiction
    ), sq_pos_of_ne_zero (show (a - b : ℝ) ≠ 0 by
      by_contra h_eq
      exfalso
      apply h_ne
      linarith
    )]
  have hr_eq_1 : r = 1 := by
    have h11_sub : r^2 + a * r + 1 = 0 := h11
    rw [h_eq3] at h11_sub
    -- Now we have r^2 - 2*r + 1 = 0
    -- This factors to (r - 1)^2 = 0
    have : (r - 1)^2 = 0 := by
      nlinarith
    -- From (r - 1)^2 = 0 we get r = 1
    have : r - 1 = 0 := by
      apply pow_eq_zero
      exact this
    -- This implies r = 1
    linarith 
  have h_eq4 : b + c = -1 := by
    rw [show (r : ℝ) = 1 by exact hr_eq_1] at h12
    nlinarith [h_eq3]
  nlinarith [h_eq3, h_eq4]