import Mathlib

theorem algebra_208537 :
  { x : ℝ |
    (9 - 3 * x) * 3 ^ x - (x - 2) * (x ^ 2 - 5 * x + 6) = 0 }
  = {3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume (9 - 3 * x) * 3 ^ x - (x - 2) * (x ^ 2 - 5 * x + 6) = 0, prove x = 3
    intro h
    have h1 : (x ^ 2 - 5 * x + 6) = (x - 2) * (x - 3) := by
      ring
    rw [h1] at h
    by_cases h2 : x < 3
    · -- Assume x < 3
      have h2' : x < 3 := h2
      have h3 : (9 - 3 * x) * (3 : ℝ) ^ x > 0 := by
        apply mul_pos
        · -- Show 9 - 3 * x > 0
          linarith
        · -- Show (3 : ℝ) ^ x > 0
          positivity
      have h4 : (x - 2) ^ 2 * (x - 3) < 0 := by
        have h5 : (x - 2) ^ 2 > 0 := by
          nlinarith [sq_nonneg (x - 2), h2']
        have h6 : x - 3 < 0 := by linarith
        nlinarith
      nlinarith [h, h3, h4]
    · -- Assume ¬(x < 3), so x ≥ 3
      have h4' : x ≥ 3 := by linarith
      by_cases h10 : x > 3
      · -- Assume x > 3
        have h2' : x > 3 := h10
        have h3 : (9 - 3 * x) * (3 : ℝ) ^ x < 0 := by
          apply mul_neg_of_neg_of_pos
          · -- Show 9 - 3 * x < 0
            linarith
          · -- Show (3 : ℝ) ^ x > 0
            positivity
        have h6 : (x - 2) ^ 2 * (x - 3) > 0 := by
          have h7 : (x - 2) ^ 2 > 0 := by
            nlinarith [sq_nonneg (x - 2), h10]
          have h8 : x - 3 > 0 := by linarith
          nlinarith
        nlinarith [h, h3, h6]
      · -- Assume ¬(x > 3), so x = 3
        have h5 : x = 3 := by linarith
        linarith
  · -- Assume x = 3, prove the equation
    intro h
    rw [h]
    norm_num