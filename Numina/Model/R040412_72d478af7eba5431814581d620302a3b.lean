import Mathlib

theorem algebra_251093 (a b : ℤ) :
    a^2 + 2 * a * b + 2 * b^2 = 13 ↔
    (a, b) = (-5, 2) ∨ (a, b) = (-1, -2) ∨ (a, b) = (1, 2) ∨
    (a, b) = (5, -2) ∨ (a, b) = (1, -3) ∨ (a, b) = (-5, 3) ∨
    (a, b) = (5, -3) ∨ (a, b) = (-1, 3) := by
  constructor
  · -- Forward direction: equation holds implies the solutions
    rintro h 
    have h1 : a^2 + 2 * a * b + 2 * b^2 = 13 := h
    have h2 : b ≤ 3 := by
      nlinarith [sq_nonneg (a + b), sq_nonneg (b - 3), sq_nonneg (a + 2 * b)]
    have h3 : b ≥ -3 := by 
      nlinarith [sq_nonneg (a + b), sq_nonneg (b + 3), sq_nonneg (a + 2 * b)]
    interval_cases b <;> try { 
      norm_num at h1
      have h4 : a ≤ 6 := by 
        nlinarith 
      have h5 : a ≥ -6 := by 
        nlinarith 
      interval_cases a <;> norm_num at h1 
      <;> simp [Prod.ext_iff] at *
      <;> tauto 
    }
  · -- Backward: solutions satisfy the equation
    rintro (h | h | h | h | h | h | h | h)
    · -- (-5, 2)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (-1, -2)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (1, 2)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (5, -2)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (1, -3)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (-5, 3)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (5, -3)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (-1, 3)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num