import Mathlib

theorem algebra_281256 :
  {m : ℝ | ∃ x1 x2 : ℝ, x1 = 2 * x2 ∧
    2 * x1 ^ 2 - (2 * m + 1) * x1 + m ^ 2 - 9 * m + 39 = 0 ∧
    2 * x2 ^ 2 - (2 * m + 1) * x2 + m ^ 2 - 9 * m + 39 = 0} = {10, 7} := by
  ext m 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume m is in the first set: i.e., there are roots with the given condition
    rintro ⟨x1, x2, h1, h2, h3⟩
    rw [h1] at h2 
    have h4 : x2 * (6 * x2 - (2 * m + 1)) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.mp h4) with h5 h6 
    · -- Case x2 = 0 
      have hx2_eq0 : x2 = 0 := by 
        linarith 
      rw [hx2_eq0] at h3 
      have h_eq_zero : m ^ 2 - 9 * m + 39 = 0 := by 
        nlinarith 
      -- $m ^ 2 - 9 * m + 39 = 0$ is a contradiction because the quadratic is positive
      have h10 : m ^ 2 - 9 * m + 39 > 0 := by 
        nlinarith [sq_nonneg (m - (9 / 2))]
      linarith 
    · -- Case 6 * x2 - (2 * m + 1) = 0 
      have h7 : x2 = (2 * m + 1) / 6 := by 
        linarith 
      rw [h7] at h3 
      have h8 : (m - 10) * (m - 7) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp h8) with h9 h10 
      · -- Case m - 10 = 0 
        left 
        linarith 
      · -- Case m - 7 = 0 
        right 
        linarith 
  · -- Assume m in {10, 7}, need to show it in the first set
    rintro (h | h) 
    · -- Case m = 10 
      rw [h] 
      use 7 
      use 3.5 
      constructor 
      · -- Show x1 = 2 * x2 
        norm_num 
      constructor
      · -- Show 2 * x1 ^ 2 - (2 * m + 1) * x1 + m ^ 2 - 9 * m + 39 = 0 
        norm_num 
      · -- Show 2 * x2 ^ 2 - (2 * m + 1) * x2 + m ^ 2 - 9 * m + 39 = 0 
        norm_num 
    · -- Case m = 7 
      rw [h] 
      use 5 
      use 2.5 
      constructor 
      · -- Show x1 = 2 * x2 
        norm_num 
      constructor
      · -- Show 2 * x1 ^ 2 - (2 * m + 1) * x1 + m ^ 2 - 9 * m + 39 = 0 
        norm_num 
      · -- Show 2 * x2 ^ 2 - (2 * m + 1) * x2 + m ^ 2 - 9 * m + 39 = 0 
        norm_num