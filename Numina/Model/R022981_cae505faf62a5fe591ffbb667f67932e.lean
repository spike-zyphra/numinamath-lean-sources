import Mathlib

theorem algebra_153323 (a : ℝ) (h : ∃ x1 x2, x1 ≠ x2 ∧ x1^2 + a * x1 + 2 = 0 ∧ x2^2 + a * x2 + 2 = 0 ∧
    x1^3 + 14 / x2^2 = x2^3 + 14 / x1^2) : a = 4 := by
  rcases h with ⟨x1, x2, h12, h1, h2, h3⟩
  have hx1 : x1 ≠ 0 := by
    by_contra h1'
    rw [h1'] at h1
    nlinarith
  have hx2 : x2 ≠ 0 := by
    by_contra h2'
    rw [h2'] at h2
    nlinarith
  have eq3 : (x1 - x2) * (x1 + x2 + a) = 0 := by
    have eq1 : x1^2 + a * x1 + 2 - (x2^2 + a * x2 + 2) = 0 := by linarith 
    have eq2 : (x1 - x2) * (x1 + x2 + a) = 0 := by 
      nlinarith 
    exact eq2
  cases' (mul_eq_zero.1 eq3) with h4 h5
  · -- Case where $x1 - x2 = 0$ which contradicts the distinct roots
    exfalso 
    apply h12
    linarith
  · -- Case where $x1 + x2 + a = 0$ 
    have sum_eq : x1 + x2 = -a := by linarith 
    have eq4 : x1 * x2 = 2 := by 
      nlinarith [sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by
        intro h0
        apply h12
        linarith
      ), sq_nonneg (x1 - x2)]
    -- Simplified the algebra to get a quadratic
    have eq5 : x1^2 + x1 * x2 + x2^2 = -7 / 2 * (x1 + x2) := by
      have eq6 : x1 ^ 3 + 14 / x2 ^ 2 = x2 ^ 3 + 14 / x1 ^ 2 := h3 
      have eq7 : (x1 - x2) * (x1^2 + x1 * x2 + x2^2) = -14 * (x1 - x2) * (x1 + x2) / (x1^2 * x2^2) := by 
        have eq8 : x1^2 * x2^2 = (x1 * x2) ^ 2 := by ring 
        have eq9 : x1 * x2 = 2 := eq4 
        have eq10 : x1^2 * x2^2 = 4 := by 
          rw [eq8, eq9]
          norm_num 
        field_simp [hx1, hx2] at eq6 ⊢
        nlinarith 
      have hx12 : x1 - x2 ≠ 0 := by
        intro h0
        apply h12
        linarith
      have h9 : x1^2 * x2^2 = 4 := by 
        calc
          x1^2 * x2^2 = (x1 * x2)^2 := by ring
          _ = 2^2 := by rw [eq4]
          _ = 4 := by norm_num
      rw [h9] at eq7 
      apply (mul_left_inj' hx12).mp
      field_simp at eq7 ⊢
      linarith 
    have eq9 : a^2 - 2 = 7 / 2 * a := by
      have eq10 : x1^2 + x1 * x2 + x2^2 = (x1 + x2)^2 - (x1 * x2) := by 
        nlinarith 
      rw [eq10] at eq5
      rw [show x1 + x2 = -a by linarith [sum_eq], eq4] at eq5 
      nlinarith 
    have eq14 : 2 * a ^ 2 - 7 * a - 4 = 0 := by
      linarith 
    have h15 : (a - 4) * (2 * a + 1) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.1 h15) with h16 h17
    · -- Case where $a - 4 = 0$, so $a = 4$
      linarith 
    · -- Case where $2a + 1 = 0$, so $a = -1/2$
      have ha : a = -1 / 2 := by linarith 
      -- This leads to complex roots, which is a contradiction
      -- As discriminant of the quadratic is (A^2-8), with A = -1/2: (1/4 - 8) < 0
      exfalso
      nlinarith [sq_pos_of_ne_zero (show x1 - x2 ≠ 0 by 
        intro h0 
        apply h12 
        linarith 
      ), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2 - (-a)), sq_nonneg (x1 * x2 - 2)]