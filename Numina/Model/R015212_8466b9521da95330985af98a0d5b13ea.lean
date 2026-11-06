import Mathlib

theorem algebra_284711 (x y : ℤ) : x + y = x^2 - x * y + y^2 ↔ (x, y) = (0, 0) ∨ (x, y) = (0, 1) ∨ (x, y) = (1, 0) ∨ (x, y) = (1, 2) ∨ (x, y) = (2, 1) ∨ (x, y) = (2, 2) := by
  constructor
  · -- Assume x + y = x^2 - x * y + y^2
    intro h
    have h1 : x ≤ 3 := by
      nlinarith [sq_nonneg (x - 2: ℤ), sq_nonneg (y - 2: ℤ), sq_nonneg (x - y: ℤ)]
    have h2 : y ≤ 3 := by
      nlinarith [sq_nonneg (x - 2: ℤ), sq_nonneg (y - 2: ℤ), sq_nonneg (x - y: ℤ)]
    have h3 : x ≥ 0 := by
      nlinarith [sq_nonneg (x - 0: ℤ), sq_nonneg (y - 0: ℤ), sq_nonneg (x - y: ℤ)]
    have h4 : y ≥ 0 := by
      nlinarith [sq_nonneg (x - 0: ℤ), sq_nonneg (y - 0: ℤ), sq_nonneg (x - y: ℤ)]
    interval_cases x <;> interval_cases y
    <;> norm_num [Prod.ext_iff] at h ⊢
    <;> omega
  · -- Assume (x, y) = (0, 0) ∨ (x, y) = (0, 1) ∨ (x, y) = (1, 0) ∨ (x, y) = (1, 2) ∨ (x, y) = (2, 1) ∨ (x, y) = (2, 2)
    rintro (h | h | h | h | h | h)
    · -- (x, y) = (0, 0)
      simp [Prod.mk.injEq] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- (x, y) = (0, 1)
      simp [Prod.mk.injEq] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- (x, y) = (1, 0)
      simp [Prod.mk.injEq] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- (x, y) = (1, 2)
      simp [Prod.mk.injEq] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- (x, y) = (2, 1)
      simp [Prod.mk.injEq] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- (x, y) = (2, 2)
      simp [Prod.mk.injEq] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num