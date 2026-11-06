import Mathlib

theorem algebra_83161 : {x : ℝ | (x - 1) * (x - 2) * (x - 3) * (x - 4) * (x - 5) * (x - 6) = 720}.encard = 2 := by
  have h1 : {x : ℝ | (x - 1) * (x - 2) * (x - 3) * (x - 4) * (x - 5) * (x - 6) = 720} = { (0 : ℝ), (7 : ℝ) } := by 
    ext x 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor 
    · -- Forward implication: If the product is 720, then x is either 0 or 7
      intro h 
      have h_eq : (x - 1) * (x - 2) * (x - 3) * (x - 4) * (x - 5) * (x - 6) = 720 := h 
      have h_eq2 : x * (x - 7) = 0 := by 
        ring_nf at h_eq
        nlinarith [sq_nonneg (x ^ 2 - 7 * x + 14), sq_nonneg (x - 7 / 2), sq_nonneg (x - 3.5), sq_nonneg ((x ^ 2 - 7 * x) + 14), sq_nonneg (x), sq_nonneg ((x - 7) ^ 2)]
      cases' (mul_eq_zero.1 h_eq2) with h0 h7 
      · -- Case x = 0 
        left 
        linarith 
      · -- Case x - 7 = 0 
        right 
        linarith 
    · -- Backward implication: If x is either 0 or 7, then the product is 720
      rintro (h | h)
      · -- Case x = 0 
        rw [h]
        norm_num 
      · -- Case x = 7 
        rw [h]
        norm_num 
  rw [h1]
  rw [Set.encard_pair]
  all_goals norm_num