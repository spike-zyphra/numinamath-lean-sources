import Mathlib

theorem algebra_316622 {a : ℝ} (ha : a^3 + a^2 - 3 * a + 2 = 3 / a - 1 / a^2 - 1 / a^3) :
    a + 1 / a = 2 ∨ a + 1 / a = -3 := by
  have ha1 : a ≠ 0 := by
    by_contra h
    rw [h] at ha
    field_simp at ha
    all_goals linarith
  have h_eq : 3 / a - 1 / a^2 - 1 / a^3 = (3 * a^2 - a - 1) / a^3 := by
    field_simp
    ring
  rw [h_eq] at ha
  have eq1 : a^6 + a^5 - 3*a^4 + 2*a^3 - 3*a^2 + a + 1 = 0 := by
    have h_eq2 : a^3 + a^2 - 3*a + 2 = (3 * a^2 - a - 1) / a^3 := ha
    have h_eq3 : (a^3 + a^2 - 3*a + 2) * a^3 = 3 * a^2 - a - 1 := by
      have h_eq5 : (a^3 + a^2 - 3*a + 2) = (3 * a^2 - a - 1) / a^3 := h_eq2
      field_simp [ha1] at h_eq5 ⊢
      nlinarith [sq_pos_of_ne_zero ha1, sq_nonneg (a^2 - a), sq_nonneg (a^2), sq_nonneg (a^3 - a^2)]
    have h_eq4 : a^6 + a^5 - 3*a^4 + 2*a^3 - 3*a^2 + a + 1 = 0 := by
      nlinarith [h_eq3, sq_nonneg (a^2 - a), sq_nonneg (a^2), sq_nonneg (a^3 - a^2), sq_nonneg (a^3 - a)]
    assumption
  have h2 : (a - 1) ^ 2 * (a^4 + 3 * a^3 + 2 * a^2 + 3 * a + 1) = 0 := by
    nlinarith [sq_nonneg (a^3 - a), sq_nonneg (a^3 - a^2), sq_nonneg (a^3 + 1), sq_nonneg (a^3 - 1)]
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- case where $(a - 1)^2 = 0$, so a = 1
    have ha2 : a = 1 := by
      nlinarith 
    left
    rw [ha2]
    norm_num
  · -- case where the quartic polynomial equals zero
    have h_eq2 : a^4 + 3*a^3 + 2*a^2 + 3*a + 1 = 0 := h4
    have eq3 : a^2 + 3*a + 2 + 3/a + 1/a^2 = 0 := by
      have h6 : a^2 + 3*a + 2 + 3/a + 1/a^2 = 0 := by
        have eq6 : a^4 + 3*a^3 + 2*a^2 + 3*a + 1 = 0 := h_eq2
        have eq7 : a^4 + 3*a^3 + 2*a^2 + 3*a + 1 = (a^2 + 3*a + 2 + 3/a + 1/a^2) * a^2 := by
          field_simp
          nlinarith
        rw [eq7] at eq6
        have h7 : a^2 ≠ 0 := by
          intro h
          apply ha1
          nlinarith
        apply (mul_right_inj' h7).mp
        linarith
      assumption
    have eq5 : (a + 1/a)^2 + 3*(a + 1/a) = 0 := by
      have eq4 : a^2 + 1/a^2 + 3*(a + 1/a) + 2 = 0 := by 
        have eq3' : a^2 + 3*a + 2 + 3/a + 1/a^2 = 0 := eq3
        have eq6 : a^2 + 3*a + 2 + 3/a + 1/a^2 = a^2 + 1/a^2 + 3*(a + 1/a) + 2 := by 
          field_simp
          ring
        rw [eq6] at eq3'
        assumption
      have h_eq5 : a^2 + 1/a^2 = (a + 1/a)^2 - 2 := by
        field_simp
        ring_nf
      rw [h_eq5] at eq4
      nlinarith
    have eq6 : (a + 1/a) * (a + 1/a + 3) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp eq6) with
    | inl h5 =>
      have eq7 : a^2 + 1 = 0 := by
        field_simp at h5
        nlinarith
      have eq10 : a^2 ≥ 0 := by
        apply sq_nonneg 
      nlinarith
    | inr h5 =>
      right 
      nlinarith