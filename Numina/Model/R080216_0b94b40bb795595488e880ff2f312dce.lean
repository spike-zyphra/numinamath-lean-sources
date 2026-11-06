import Mathlib

theorem algebra_278065 (a b : ℤ) : 7 * a + 14 * b = 5 * a ^ 2 + 5 * a * b + 5 * b ^ 2 ↔
    (a, b) = (-1, 3) ∨ (a, b) = (0, 0) ∨ (a, b) = (1, 2) := by
  constructor
  · -- Forward: equation implies solutions
    rintro h
    have h1 : 5 * a ^ 2 + 5 * a * b + 5 * b ^ 2 = 7 * a + 14 * b := by linarith
    have h2 : a ≤ 4 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 2), sq_nonneg (a + 1), sq_nonneg (b - 3), sq_nonneg (a - 1 : ℤ), sq_nonneg (b : ℤ), sq_nonneg (a - 1 : ℤ), sq_nonneg (b : ℤ)]
    have h3 : b ≤ 4 := by
      nlinarith [sq_nonneg (a - 1 : ℤ), sq_nonneg (b - 2 : ℤ), sq_nonneg (a + 1 : ℤ), sq_nonneg (b - 3 : ℤ), sq_nonneg (a - 1 : ℤ), sq_nonneg (b : ℤ)]
    have h4 : a ≥ -3 := by
      nlinarith [sq_nonneg (a - 1 : ℤ), sq_nonneg (b - 2 : ℤ), sq_nonneg (a + 1 : ℤ), sq_nonneg (b - 3 : ℤ), sq_nonneg (a - 1 : ℤ), sq_nonneg (b : ℤ)]
    have h5 : b ≥ -1 := by
      nlinarith [sq_nonneg (a - 1 : ℤ), sq_nonneg (b - 2 : ℤ), sq_nonneg (a + 1 : ℤ), sq_nonneg (b - 3 : ℤ), sq_nonneg (a - 1 : ℤ), sq_nonneg (b : ℤ)]
    interval_cases a <;> interval_cases b <;> norm_num at h1 <;> tauto
  · -- Backward: solutions satisfy equation
    rintro (h | h | h)
    · -- (-1, 3)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- (0, 0)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- (1, 2)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num