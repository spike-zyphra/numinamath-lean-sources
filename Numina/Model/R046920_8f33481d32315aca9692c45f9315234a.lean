import Mathlib

theorem algebra_255710 :
  { (x, z) : ℝ × ℝ | 
    x ≠ 1/6 ∧ x ≠ -1/6 ∧ 
    z ≠ 1 ∧ z ≠ -1 ∧
    3 / (1 - 6 * x) = 2 / (6 * x + 1) - (8 + 9 * x) / (36 * x ^ 2 - 1) ∧ 
    3 / (1 - z ^ 2) = 2 / (1 + z) ^ 2 - 5 / (1 - z) ^ 2 
  } = { (1/3, -3/7) } := by
  ext ⟨x, z⟩
  simp [-one_div]
  constructor
  · -- Assume (x, z) satisfies the conditions, prove (x, z) = (1/3, -3/7)
    rintro ⟨hx1, hx2, hz1, hz2, heq1, heq2⟩
    have h_eq1 : 3 / (1 - 6 * x) = 2 / (6 * x + 1) - (8 + 9 * x) / (36 * x ^ 2 - 1) := by
      linarith [heq1]
    have h_eq2 : 3 / (1 - z ^ 2) = 2 / (1 + z) ^ 2 - 5 / (1 - z) ^ 2 := by 
      linarith [heq2]
    have eq2 : x - 1 / 3 = 0 := by
      have h1 : 1 - 6 * x ≠ 0 := by
        by_contra h
        have h2 : x = 1 / 6 := by
          linarith
        contradiction
      have h2 : 6 * x + 1 ≠ 0 := by
        by_contra h
        have h3 : x = -1 / 6 := by
          linarith
        contradiction
      have h3 : (36 * x ^ 2 - 1 : ℝ) ≠ 0 := by
        by_contra h
        have h4 : x = 1 / 6 ∨ x = -1 / 6 := by
          have h5 : 36 * x ^ 2 - 1 = 0 := by linarith
          have h6 : 36 * x ^ 2 = 1 := by linarith
          have h7 : (6 * x) ^ 2 = 1 := by
            nlinarith
          have h8 : 6 * x = 1 ∨ 6 * x = -1 := by
            rw [sq_eq_one_iff] at h7
            tauto
          cases h8 with
          | inl h9 =>
            left
            linarith
          | inr h10 =>
            right
            linarith
        cases h4 with
        | inl h5 =>
          contradiction
        | inr h6 =>
          contradiction
      have eq5 : 3 * (6 * x + 1) = 2 * (1 - 6 * x) + (8 + 9 * x) := by
        have eq2 : 1 - 6 * x ≠ 0 := h1
        have eq3 : 6 * x + 1 ≠ 0 := h2
        have eq4 : (36 * x ^ 2 - 1 : ℝ) ≠ 0 := h3
        field_simp [eq2, eq3, eq4] at h_eq1 ⊢ 
        nlinarith [sq_pos_of_ne_zero (show (1 - 6 * x) ≠ 0 by assumption), sq_pos_of_ne_zero (show (6 * x + 1) ≠ 0 by assumption), sq_pos_of_ne_zero (show (36 * x ^ 2 - 1 : ℝ) ≠ 0 by assumption)]
      nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (x - 1 / 6), sq_pos_of_ne_zero (show (x - 1 / 6) ≠ 0 by 
        intro h'
        apply hx1
        linarith 
      ), sq_nonneg (x - 1 / 3)]
    have hx3 : x = 1 / 3 := by linarith
    -- Solve for z 
    have eq7 : z = -3 / 7 := by 
      -- Check denominators are non-zero 
      have h11 : (1 - z ^ 2 : ℝ) ≠ 0 := by
        by_contra h
        have h4 : z ^ 2 = 1 := by nlinarith
        have h5 : z = 1 ∨ z = -1 := by 
          have h6 : z ^ 2 = 1 := h4
          rw [sq_eq_one_iff] at h6
          tauto
        cases h5 with 
        | inl h6 =>
          contradiction
        | inr h7 =>
          contradiction
      -- Solve remaining equations using non-zero denominators 
      have h12 : (1 + z) ^ 2 ≠ 0 := by
        by_contra h
        have h4 : 1 + z = 0 := by 
          apply pow_eq_zero 
          exact h
        have h5 : z = -1 := by linarith 
        contradiction 
      have h13 : (1 - z) ^ 2 ≠ 0 := by 
        by_contra h
        have h4 : 1 - z = 0 := by 
          apply pow_eq_zero 
          exact h 
        have h5 : z = 1 := by linarith 
        contradiction 
      -- Use field_simp to clear denominators 
      field_simp [h11, h12, h13] at h_eq2 ⊢
      -- Solve the resulting polynomial using nlinarith 
      nlinarith [sq_pos_of_ne_zero (show (1 - z ^ 2 : ℝ) ≠ 0 by assumption), sq_pos_of_ne_zero (show (1 + z : ℝ) ≠ 0 by 
        by_contra h
        have : z = -1 := by linarith 
        contradiction 
      ), sq_pos_of_ne_zero (show (1 - z : ℝ) ≠ 0 by 
        by_contra h
        have : z = 1 := by linarith 
        contradiction 
      ), sq_nonneg (z + 3 / 7)]
    -- Conclusion
    simp [hx3, eq7]
  · -- Assume (x, z) = (1/3, -3/7), prove all conditions
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num