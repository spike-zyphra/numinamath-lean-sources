import Mathlib

theorem algebra_253047 (a b : ℤ) :
    7 * a + 14 * b = 5 * a ^ 2 + 5 * a * b + 5 * b ^ 2 ↔
    (a, b) = (-1, 3) ∨ (a, b) = (0, 0) ∨ (a, b) = (1, 2) := by
  constructor
  · -- Assume 7a + 14b = 5a^2 + 5ab + 5b^2, prove the disjunction of the three pairs
    intro h
    have h1 : 5 * a ^ 2 + 5 * a * b + 5 * b ^ 2 = 7 * a + 14 * b := by linarith
    have h3 : a ≤ 5 := by
      nlinarith [sq_nonneg (a - 1 : ℤ), sq_nonneg (b - 2 : ℤ), sq_nonneg (a + 1 : ℤ), sq_nonneg (b - 3 : ℤ), sq_nonneg (a : ℤ), sq_nonneg (b : ℤ)]
    have h4 : a ≥ -4 := by
      nlinarith [sq_nonneg (a - 1 : ℤ), sq_nonneg (b - 2 : ℤ), sq_nonneg (a + 1 : ℤ), sq_nonneg (b - 3 : ℤ), sq_nonneg (a : ℤ), sq_nonneg (b : ℤ)]
    have h5 : b ≤ 4 := by
      nlinarith [sq_nonneg (a - 1 : ℤ), sq_nonneg (b - 2 : ℤ), sq_nonneg (a + 1 : ℤ), sq_nonneg (b - 3 : ℤ), sq_nonneg (a : ℤ), sq_nonneg (b : ℤ)]
    have h6 : b ≥ -2 := by
      nlinarith [sq_nonneg (a - 1 : ℤ), sq_nonneg (b - 2 : ℤ), sq_nonneg (a + 1 : ℤ), sq_nonneg (b - 3 : ℤ), sq_nonneg (a : ℤ), sq_nonneg (b : ℤ)]
    interval_cases a <;> interval_cases b <;> norm_num [Prod.ext_iff] at h ⊢ <;> tauto
  · -- Assume the disjunction of the three pairs, prove the equation
    rintro (h | h | h)
    · -- (a, b) = (-1, 3)
      simp [Prod.ext_iff] at h
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (a, b) = (0, 0)
      simp [Prod.ext_iff] at h
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (a, b) = (1, 2)
      simp [Prod.ext_iff] at h
      rcases h with ⟨rfl, rfl⟩
      norm_num