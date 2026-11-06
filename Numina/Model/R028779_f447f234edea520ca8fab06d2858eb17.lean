import Mathlib

theorem algebra_235432 (x : ℝ) :
    8 * (Real.cos x)^5 - 5 * Real.cos x - 2 * Real.cos (3 * x) = 1 ↔
    ∃ n : ℤ, x = 2 * Real.pi * n := by 
  constructor
  · -- Assume the equation holds, prove x = 2πn for some n ∈ ℤ
    intro h
    have h1 : Real.cos (3 * x) = 4 * (Real.cos x) ^ 3 - 3 * Real.cos x := by 
      rw [Real.cos_three_mul]
    rw [h1] at h
    have h2 : 8 * (Real.cos x) ^ 5 - 8 * (Real.cos x) ^ 3 + Real.cos x - 1 = 0 := by 
      nlinarith 
    have h3 : (Real.cos x - 1) * (8 * (Real.cos x) ^ 4 + 8 * (Real.cos x) ^ 3 + 1) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- Case where Real.cos x - 1 = 0, so Real.cos x = 1 
      have h6 : Real.cos x = 1 := by linarith 
      have h7 : ∃ n : ℤ, x = 2 * Real.pi * n := by 
        have h8 : Real.cos x = 1 := h6 
        rw [Real.cos_eq_one_iff] at h8 
        rcases h8 with ⟨n, hn⟩
        refine ⟨n, by 
          linarith 
        ⟩
      exact h7 
    · -- Case where 8 * (Real.cos x) ^ 4 + 8 * (Real.cos x) ^ 3 + 1 = 0 
      have h6 : 8 * (Real.cos x) ^ 4 + 8 * (Real.cos x) ^ 3 + 1 = 0 := by 
        nlinarith
      have h7 : -1 ≤ Real.cos x ∧ Real.cos x ≤ 1 := by 
        constructor 
        · -- Show that -1 ≤ Real.cos x 
          nlinarith [Real.neg_one_le_cos x]
        · -- Show that Real.cos x ≤ 1 
          nlinarith [Real.cos_le_one x]
      nlinarith [sq_nonneg ((Real.cos x) + 3 / 4), sq_nonneg ((Real.cos x) ^ 2 - 9 / 16), sq_nonneg ((Real.cos x) + 1), sq_nonneg ((Real.cos x) - (-3 / 4)), sq_nonneg ((Real.cos x) ^ 2 + (Real.cos x) * (4 / 3)), sq_nonneg ((Real.cos x) * 4 + 3), sq_nonneg ((Real.cos x) + 1 / 2)]
  · -- Assume there's integer n with x = 2 * Real.pi * n, prove the original equation
    rintro ⟨n, hn⟩ 
    have h10 : Real.cos x = 1 := by 
      rw [show x = 2 * Real.pi * (n : ℝ) by linarith [hn]]
      have h11 : Real.cos (2 * Real.pi * (n : ℝ)) = 1 := by 
        have h5 : 2 * Real.pi * (n : ℝ) = (n : ℝ) * (2 * Real.pi) := by ring 
        rw [h5] 
        have h10 : Real.cos ((n : ℝ) * (2 * Real.pi)) = 1 := by 
          have h11 : (n : ℝ) * (2 * Real.pi) = (n : ℤ) * (2 * Real.pi) := by 
            simp 
          rw [h11] 
          exact Real.cos_int_mul_two_pi n 
        exact h10 
      exact h11 
    have h11 : Real.cos (3 * x) = 1 := by
      have h10' : Real.cos x = 1 := h10 
      have h11 : Real.cos (3 * x) = 4 * (Real.cos x) ^ 3 - 3 * Real.cos x := by 
        rw [Real.cos_three_mul]
      rw [h11, h10']
      norm_num 
    rw [h10, h11] 
    all_goals nlinarith