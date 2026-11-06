import Mathlib

theorem algebra_200090 (f : ℝ → ℝ) (hf : f = fun x => abs x - 4 / x - 3 * abs x / x) :
    Set.ncard {x | x ≠ 0 ∧ f x = 0} = 1 := by
  have h1 : {x | x ≠ 0 ∧ f x = 0} = {4} := by 
    ext x 
    simp [hf]
    constructor 
    · -- Assume x in {x | x ≠ 0 ∧ f x = 0}, show x = 4
      intro h 
      rcases h with ⟨hx1, hx2⟩ 
      by_cases h2 : x > 0
      · -- Case x > 0
        have h3 : abs x = x := abs_of_pos h2
        field_simp [h3] at hx2
        have h4 : x ^ 2 - 3 * x - 4 = 0 := by 
          nlinarith 
        have h5 : (x - 4) * (x + 1) = 0 := by 
          nlinarith 
        cases' (mul_eq_zero.1 h5) with h6 h7
        · -- Case x - 4 = 0
          linarith 
        · -- Case x + 1 = 0 
          nlinarith 
      · -- Case x ≤ 0 
        have h3 : x < 0 := by 
          by_contra h3
          push_neg at h3
          have : x = 0 := by linarith 
          contradiction 
        have h4 : abs x = -x := abs_of_neg h3 
        field_simp [h4] at hx2 
        nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 4), sq_pos_of_neg h3, sq_nonneg (x - 3)]
    · -- Assume x = 4, show in {x | x ≠ 0 ∧ f x = 0}
      intro h 
      rw [h] 
      constructor 
      · norm_num 
      · -- Show f(4) = 0 
        norm_num [abs_of_nonneg]
  rw [h1] 
  norm_num