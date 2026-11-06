import Mathlib
/-If the product of the roots of the equation 9x^2-6(a+1)x+a^2-3=0
is equal to 1. then the value of a is ?-/
theorem algebra_2150
    (a : ℝ)
    (h : ∃ x0 x1 : ℝ, x0 ≠ x1 ∧ 9 * x0 ^ 2 - 6 * (a + 1) * x0 + a ^ 2 - 3 = 0 ∧ 9 * x1 ^ 2 - 6 * (a + 1) * x1 + a ^ 2 - 3 = 0 ∧ x0 * x1 = 1) :
    a = 2 * Real.sqrt 3 := by 
  obtain ⟨x0, x1, hx01, h0, h1, hprod⟩ := h

  have hsum : (x0 + x1) = 2 * (a + 1) / 3 := by -- use factorization
    have h2 : 9 * x0 ^ 2 - 6 * (a + 1) * x0 + a ^ 2 - 3 = 0 := h0
    have h3 : 9 * x1 ^ 2 - 6 * (a + 1) * x1 + a ^ 2 - 3 = 0 := h1
    have h_sub : 9 * (x0^2 - x1^2) - 6 * (a + 1) * (x0 - x1) = 0 := by 
      nlinarith
    have h4 : (x0 - x1) ≠ 0 := sub_ne_zero.mpr hx01
    have h5 : 9 * (x0 + x1) - 6 * (a + 1) = 0 := by 
      apply (mul_left_inj' h4).mp
      nlinarith
    linarith

  have h_eq1 : a ^ 2 = 12 := by --express x0^2+x1^2 in two ways
    have h6 : 9 * (x0 ^ 2 + x1 ^ 2) + 2 * (a ^ 2 - 3) = 4 * (a + 1) ^ 2 := by
      have h_eq2 : 9 * x0 ^ 2 + a ^ 2 - 3 = 6 * (a + 1) * x0 := by linarith [h0]
      have h_eq3 : 9 * x1 ^ 2 + a ^ 2 - 3 = 6 * (a + 1) * x1 := by linarith [h1]
      have h_add : 9 * (x0 ^ 2 + x1 ^ 2) + 2 * (a ^ 2 - 3) = 6 * (a + 1) * (x0 + x1) := by 
        linarith
      nlinarith [hsum]
    have h_eq3 : x0 ^ 2 + x1 ^ 2 = (4 * (a + 1) ^ 2) / 9 - 2 := by
      have h_sq : (x0 + x1) ^ 2 = x0 ^ 2 + 2 * (x0 * x1) + x1 ^ 2 := by ring
      have h_eq5 : x0 ^ 2 + x1 ^ 2 = (x0 + x1) ^ 2 - 2 * (x0 * x1) := by 
        linarith [h_sq]
      rw [h_eq5, hsum, hprod]
      ring
    nlinarith [h_eq3, h6]

  have h8 : a = 2 * Real.sqrt 3 ∨ a = -2 * Real.sqrt 3 := by 
    have h9 : a ^ 2 - 12 = 0 := by linarith
    have h10 : (a - 2 * Real.sqrt 3) * (a + 2 * Real.sqrt 3) = 0 := by
      have h11 : (2 * Real.sqrt 3) ^ 2 = 12 := by
        calc
          (2 * Real.sqrt 3) ^ 2 = 4 * (Real.sqrt 3 ^ 2) := by ring
          _ = 4 * 3 := by rw [Real.sq_sqrt]; linarith
          _ = 12 := by norm_num
      ring_nf
      nlinarith [h11, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    cases' (mul_eq_zero.mp h10) with h12 h13
    · left
      linarith
    · right
      linarith

  cases' h8 with h14 h15
  · exact h14
  · -- Prove that $a > -2$ from the existence of two distinct real roots
    have h16 : a > -2 := by 
      have h17 : (x0 - x1) ^ 2 > 0 := by 
        apply sq_pos_of_ne_zero
        exact sub_ne_zero.mpr hx01
      have h18 : (x0 - x1) ^ 2 = ((2 * (a + 1) / 3) ^ 2 - 4 * 1) := by 
        have h19 : (x0 - x1) ^ 2 = (x0 + x1) ^ 2 - 4 * (x0 * x1) := by 
          ring_nf
        rw [h19, hsum, hprod]
      have h20 : ((2 * (a + 1) / 3) ^ 2 - 4 * 1) > 0 := by 
        nlinarith [h17, h18]
      nlinarith [sq_nonneg (a + 1), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    have h21 : False := by 
      have h22 : Real.sqrt 3 > 0 := Real.sqrt_pos.2 (by norm_num)
      nlinarith [h15, h22]
    exact False.elim h21