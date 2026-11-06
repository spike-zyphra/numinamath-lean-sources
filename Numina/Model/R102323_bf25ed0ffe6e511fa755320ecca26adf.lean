import Mathlib

theorem algebra_289832 (a : ℤ) :
    (∃ x1 x2 : ℤ, x1 ≠ x2 ∧ 2*x1^2-a*x1+2*a=0 ∧ 2*x2^2-a*x2+2*a=0) ↔
    a = -2 ∨ a = 18 := by
  constructor
  · -- Assume there exists two distinct integer roots, prove possible values of a
    rintro ⟨x1, x2, hx12, h1, h2⟩
    have h3 : (x1 - x2) ≠ 0 := sub_ne_zero_of_ne hx12
    -- Subtract the two equations to eliminate quadratic terms
    have h_sub : (x1 - x2) * (2 * (x1 + x2) - a) = 0 := by
      nlinarith
    cases (mul_eq_zero.1 h_sub) with
    | inl h4 =>
      exfalso
      exact hx12 (by linarith)
    | inr h5 =>
      have ha1 : a = 2 * (x1 + x2) := by linarith
      rw [ha1] at h1 h2
      -- Derive relations from equation
      have h_eq : x1 * x2 = 2 * (x1 + x2) := by
        nlinarith [sq_pos_of_ne_zero (show (x1 - x2) ≠ 0 by exact h3), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2)]
      have h_eq2 : (x1 - 2) * (x2 - 2) = 4 := by
        nlinarith [h_eq]
      have h6 : x1 ≤ 6 := by
        have h12 : x1 - 2 ∣ 4 := by
          use (x2 - 2)
          nlinarith
        have h7 : x1 - 2 ≤ 4 := by
          apply Int.le_of_dvd (show (0 : ℤ) < 4 by norm_num) h12
        omega
      have h7 : x1 ≥ -2 := by
        have h12 : x1 - 2 ∣ 4 := by
          use (x2 - 2)
          nlinarith
        have h8 : x1 - 2 ≥ -4 := by
          have h9 : (- (x1 - 2)) ∣ 4 := by
            exact Int.neg_dvd.2 h12
          have h10 : - (x1 - 2) ≤ 4 := by
            apply Int.le_of_dvd (show (0 : ℤ) < 4 by norm_num) h9
          linarith
        omega
      interval_cases x1 <;> try { 
        omega
      } <;> norm_num at h_eq2 <;> norm_num [ha1] at *
      <;> omega
  · -- Assume a is -2 or 18, prove existence of two distinct integer roots
    rintro (ha | ha)
    · -- Case a = -2
      rw [ha]
      use -2, 1
      constructor
      · -- Show -2 ≠ 1
        norm_num
      constructor
      · -- Verify first root
        norm_num
      · -- Verify second root
        norm_num
    · -- Case a = 18
      rw [ha]
      use 3, 6
      constructor
      · -- Show 3 ≠ 6
        norm_num
      constructor
      · -- Verify first root
        norm_num
      · -- Verify second root
        norm_num