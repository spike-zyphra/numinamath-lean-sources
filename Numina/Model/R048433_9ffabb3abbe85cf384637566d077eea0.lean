import Mathlib

theorem algebra_203943 {x1 x2 : ℝ} (hx : x1^2 + 5 * x1 + 1 = 0 ∧ x2^2 + 5 * x2 + 1 = 0)
    (hx12 : x1 ≠ x2) :
    ((x1 * Real.sqrt 6) / (1 + x2))^2 + ((x2 * Real.sqrt 6) / (1 + x1))^2 = 220 := by 
  rcases hx with ⟨h1, h2⟩ 
  have h3 : x1 + x2 = -5 := by
    have eq1 : x1^2 + 5 * x1 + 1 = 0 := h1
    have eq2 : x2^2 + 5 * x2 + 1 = 0 := h2
    have eq3 : x1^2 + 5 * x1 + 1 - (x2^2 + 5 * x2 + 1) = 0 := by
      linarith
    have eq4 : (x1 - x2) * (x1 + x2 + 5) = 0 := by 
      ring_nf at eq3 ⊢
      linarith
    cases (mul_eq_zero.mp eq4) with
    | inl h => 
      exfalso
      apply hx12
      linarith
    | inr h =>
      linarith
  have h4 : x1 * x2 = 1 := by
    nlinarith [sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by 
      intro h'
      apply hx12
      linarith), h3]
  have eq1 : ((x1 * Real.sqrt 6) / (1 + x2))^2 + ((x2 * Real.sqrt 6) / (1 + x1))^2 =
      6 * (x1^2 / (1 + x2)^2 + x2^2 / (1 + x1)^2) := by 
    have h11 : ((x1 * Real.sqrt 6) / (1 + x2))^2 = 6 * (x1^2 / (1 + x2)^2) := by 
      field_simp [(show (1 + x2) ≠ 0 by
        by_contra h
        have h5 : x2 = -1 := by linarith 
        rw [h5] at h2 
        nlinarith
        )]
      <;> ring_nf <;> norm_num [Real.sq_sqrt]
    have h12 : ((x2 * Real.sqrt 6) / (1 + x1))^2 = 6 * (x2^2 / (1 + x1)^2) := by 
      field_simp [(show (1 + x1) ≠ 0 by
        by_contra h
        have h5 : x1 = -1 := by linarith 
        rw [h5] at h1 
        nlinarith
        )]
      <;> ring_nf <;> norm_num [Real.sq_sqrt]
    linarith [h11, h12]
  rw [eq1]
  have eq2 : x1^2 / (1 + x2)^2 + x2^2 / (1 + x1)^2 = 110 / 3 := by
    have eq5 : (1 + x2)^2 * (1 + x1)^2 = 9 := by
      have eq8 : (1 + x1) * (1 + x2) = -3 := by
        nlinarith [h3, h4]
      nlinarith [eq8]
    have eq6 : x1^2 * (1 + x1)^2 + x2^2 * (1 + x2)^2 = 330 := by
      nlinarith [sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by
        intro h'
        apply hx12
        linarith), pow_two_nonneg (x1 - x2), h3, h4, 
          sq_nonneg (x1 + x2), sq_nonneg (x1 - x2)]
    field_simp [(show (1 + x2) ≠ 0 by
      by_contra h
      have h5 : x2 = -1 := by linarith 
      rw [h5] at h2 
      nlinarith
      ), (show (1 + x1) ≠ 0 by
        by_contra h
        have h5 : x1 = -1 := by linarith 
        rw [h5] at h1 
        nlinarith
        )] 
    <;> nlinarith [eq6, eq5]
  nlinarith [eq2]