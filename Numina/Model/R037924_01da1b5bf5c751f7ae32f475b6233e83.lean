import Mathlib

theorem algebra_4200 : (∑ᶠ x ∈ {x : ℝ | 0 ≤ 2 * x ^ 2 + 1 ∧ Real.sqrt (2 * x ^ 2 + 1) = Real.sqrt 19}, x) / {x : ℝ | 0 ≤ 2 * x ^ 2 + 1 ∧ Real.sqrt (2 * x ^ 2 + 1) = Real.sqrt 19}.ncard = 0 := by
  have h1 : {x : ℝ | 0 ≤ 2 * x ^ 2 + 1 ∧ Real.sqrt (2 * x ^ 2 + 1) = Real.sqrt 19} = {3, -3} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x in the left side set, prove x in right side set.
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : 2 * x ^ 2 + 1 = 19 := by
        have h4 : Real.sqrt (2 * x ^ 2 + 1) = Real.sqrt (19) := by
          simpa using h2
        have h5 : (Real.sqrt (2 * x ^ 2 + 1)) ^ 2 = (Real.sqrt (19 : ℝ)) ^ 2 := by
          rw [h4]
        have h6 : (Real.sqrt (2 * x ^ 2 + 1)) ^ 2 = 2 * x ^ 2 + 1 := Real.sq_sqrt (by linarith)
        have h7 : (Real.sqrt (19 : ℝ)) ^ 2 = 19 := Real.sq_sqrt (by norm_num)
        nlinarith [h5, h6, h7]
      have h4 : x ^ 2 = 9 := by
        linarith
      have h5 : x = 3 ∨ x = -3 := by
        have h : x^2 - 9 = 0 := by linarith
        have h6 : (x - 3) * (x + 3) = 0 := by
          nlinarith
        cases (mul_eq_zero.1 h6) with
        | inl h7 => 
          left 
          linarith
        | inr h8 => 
          right 
          linarith
      tauto 
    · -- Assume x in the right side set, prove x in left side set.
      rintro (h | h)
      · -- x = 3
        rw [h]
        constructor
        · norm_num
        · -- Show that √(2 * 3 ^2 +1 ) = √19
          have h1 : Real.sqrt (2 * (3 : ℝ) ^ 2 + 1) = Real.sqrt 19 := by
            norm_num
          exact h1
      · -- x = -3
        rw [h]
        constructor
        · norm_num
        · -- Show that √(2 * (-3) ^2 +1 ) = √19
          have h1 : Real.sqrt (2 * (-3 : ℝ) ^ 2 + 1) = Real.sqrt 19 := by
            norm_num
          exact h1
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num