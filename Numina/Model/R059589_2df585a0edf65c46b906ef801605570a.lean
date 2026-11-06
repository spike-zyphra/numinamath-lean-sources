import Mathlib

theorem algebra_11907: ∑ᶠ x ∈ {(x):ℝ | (x ^ 2 + 4 * x + 1) ≠ 0 ∧ (x ^ 2 - 10 * x) ≠ 0 ∧ (x - 2) / (x ^ 2 + 4 * x + 1) = (x - 5) / (x ^ 2 - 10 * x)}, x = 39/11 := by
  have h1 : {(x):ℝ | (x ^ 2 + 4 * x + 1) ≠ 0 ∧ (x ^ 2 - 10 * x) ≠ 0 ∧ (x - 2) / (x ^ 2 + 4 * x + 1) = (x - 5) / (x ^ 2 - 10 * x)} = { (39 + Real.sqrt 1741) / 22, (39 - Real.sqrt 1741) / 22 } := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x satisfies the original equation and denominators are non-zero
      rintro ⟨h1, h2, heq⟩
      have h3 : (x - 2) * (x^2 - 10 * x) = (x - 5) * (x^2 + 4 * x + 1) := by
        have h1' : x^2 + 4 * x + 1 ≠ 0 := h1
        have h2' : x^2 - 10 * x ≠ 0 := h2
        field_simp [h1', h2'] at heq ⊢
        nlinarith
      have h : 11 * x^2 - 39 * x - 5 = 0 := by
        nlinarith [h3]
      have h4 : (x - (39 + Real.sqrt 1741) / 22) * (x - (39 - Real.sqrt 1741) / 22) = 0 := by
        nlinarith [h, Real.sqrt_pos.mpr (show (0 : ℝ) < 1741 by norm_num : (0 : ℝ) < 1741), Real.sq_sqrt (show (0 : ℝ) ≤ 1741 by norm_num : (0 : ℝ) ≤ 1741)]
      cases' (mul_eq_zero.mp h4) with h5 h6
      · -- Case where x equals the first root
        left
        linarith
      · -- Case where x equals the second root
        right
        linarith
    · -- Show that the two quadratic roots satisfy the original equation
      rintro (h | h)
      · -- First root
        have hx1 : x = (39 + Real.sqrt 1741) / 22 := by linarith
        have eq1 : 11 * x^2 - 39 * x - 5 = 0 := by
          rw [hx1]
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 1741 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 1741 by norm_num)]
        have h1 : x^2 + 4 * x + 1 ≠ 0 := by 
          by_contra H
          nlinarith [sq_nonneg (x + 2), sq_pos_of_ne_zero (show Real.sqrt 1741 ≠ 0 by positivity), sq_nonneg (x + 2 - (Real.sqrt 1741)/22*2), sq_nonneg (x + 2 + (Real.sqrt 1741)/22*2)]
        have h2 : x^2 - 10 * x ≠ 0 := by 
          by_contra H
          nlinarith [sq_pos_of_ne_zero (show Real.sqrt 1741 ≠ 0 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ 1741 by norm_num)]
        have heq : (x - 2) / (x^2 + 4 * x + 1) = (x - 5) / (x^2 - 10 * x) := by
          have h3 : (x - 2) * (x^2 - 10 * x) = (x - 5) * (x^2 + 4 * x + 1) := by
            nlinarith [eq1]
          field_simp [h1, h2] at *
          nlinarith
        constructor
        · exact h1
        constructor
        · exact h2
        · exact heq
      · -- Second root
        have hx2 : x = (39 - Real.sqrt 1741) / 22 := by linarith
        have eq1 : 11 * x^2 - 39 * x - 5 = 0 := by
          rw [hx2]
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 1741 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 1741 by norm_num)]
        have h1 : x^2 + 4 * x + 1 ≠ 0 := by 
          by_contra H
          nlinarith [sq_nonneg (x + 2), sq_pos_of_ne_zero (show Real.sqrt 1741 ≠ 0 by positivity), sq_nonneg (x + 2 - (Real.sqrt 1741)/22*2), sq_nonneg (x + 2 + (Real.sqrt 1741)/22*2)]
        have h2 : x^2 - 10 * x ≠ 0 := by 
          by_contra H
          nlinarith [sq_pos_of_ne_zero (show Real.sqrt 1741 ≠ 0 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ 1741 by norm_num)]
        have heq : (x - 2) / (x^2 + 4 * x + 1) = (x - 5) / (x^ 2 - 10 * x) := by
          have h3 : (x - 2) * (x^2 - 10 * x) = (x - 5) * (x^2 + 4 * x + 1) := by
            nlinarith [eq1]
          field_simp [h1, h2] at *
          nlinarith
        constructor
        · exact h1
        constructor
        · exact h2
        · exact heq
  rw [h1]
  rw [finsum_mem_pair (by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 1741 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 1741 by norm_num)])]
  field_simp
  <;> ring