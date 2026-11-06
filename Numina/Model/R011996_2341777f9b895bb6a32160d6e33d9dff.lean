import Mathlib

theorem number_theory_70844: {(x, y): ℤ × ℤ | 8 * x ^ 2 * y ^ 2 + x ^ 2 + y ^ 2 = 10 * x * y} =
  {(0, 0), (1, 1), (-1, -1)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Forward
    rintro h
    have h2 : (x * y) ≤ 1 := by nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x + 1), sq_nonneg (y + 1)]
    have h3 : (x * y) ≥ 0 := by nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (x + 1), sq_nonneg (y + 1)]
    have h4 : x * y = 0 ∨ x * y = 1 := by
      interval_cases h5 : x * y <;> omega
    rcases h4 with h4 | h4
    · -- Case where x * y = 0
      have h5 : x = 0 ∨ y = 0 := by
        cases (mul_eq_zero.1 h4) with
        | inl h6 => 
          left
          linarith
        | inr h7 => 
          right
          linarith
      rcases h5 with h5 | h5
      · -- x = 0
        have h6 : y = 0 := by
          rw [h5] at h
          nlinarith
        simp [h5, h6]
      · -- y = 0
        have h7 : x = 0 := by
          rw [h5] at h
          nlinarith
        simp [h7, h5]
    · -- Case where x * y = 1
      have h5 : x ^ 2 + y ^ 2 = 2 := by
        nlinarith
      have h6 : (x - y) ^ 2 = 0 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
      have h7 : x = y := by
        nlinarith
      have h8 : x ^ 2 = 1 := by
        rw [show y = x by linarith [h7]] at h5
        nlinarith
      have h9 : x = 1 ∨ x = -1 := by 
        rw [sq_eq_one_iff] at h8
        tauto
      rcases h9 with h9 | h9
      · -- Case where x = 1
        have h10 : y = 1 := by
          rw [show x = 1 by linarith] at h7
          linarith
        simp [h9, h10]
      · -- Case where x = -1
        have h10 : y = -1 := by
          rw [show x = -1 by linarith] at h7
          linarith
        simp [h9, h10]
  · -- Backward
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- (0, 0)
      norm_num
    · -- (1, 1)
      norm_num
    · -- (-1, -1)
      norm_num