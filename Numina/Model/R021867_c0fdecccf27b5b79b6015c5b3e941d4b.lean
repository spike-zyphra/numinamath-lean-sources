import Mathlib

theorem algebra_223886 (x y : ℤ) :
    x^3 + y^3 = (x + y)^2 ↔ ∃ k, (x, y) = (k, -k) ∨
      (x, y) = (2, 2) ∨ (x, y) = (1, 0) ∨ (x, y) = (1, 2) ∨
      (x, y) = (0, 1) ∨ (x, y) = (2, 1) := by
  constructor
  · -- Forward direction: equation implies solutions
    intro h
    have h1 : x^3 + y^3 = (x + y)^2 := h

    by_cases h2 : x + y = 0
    · -- Assume x + y = 0. So y = -x. Now show it's a solution.
      have h3 : y = -x := by
        linarith
      use x
      left
      simp [h3]
    · -- Case where x + y ≠ 0.
      have h3 : x^3 + y^3 = (x + y)^2 := h1
      have h4 : (x + y) * (x^2 - x * y + y^2) = (x + y) * (x + y) := by
        linarith [h3]
      have h5 : x^2 - x * y + y^2 = x + y := by
        apply (mul_left_inj' h2).mp
        linarith
      have h7 : x ≤ 3 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x + y - 2)]
      have h8 : y ≤ 3 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x + y - 2)]
      have h9 : x ≥ -1 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x + y - 2)]
      have h10 : y ≥ -1 := by
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (x + y - 2)]
      use 0
      right
      interval_cases x <;> interval_cases y
      <;> norm_num [Prod.ext_iff] at h1 h5 ⊢
      <;> tauto
  · -- Backward direction: solutions satisfy the equation
    rintro ⟨k, h⟩
    rcases h with (h | h | h | h | h | h)
    · -- Assume (x,y) = (k, -k)
      simp [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      all_goals
        ring
    · -- Assume (x,y) = (2,2)
      simp [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      all_goals
        ring
    · -- Assume (x,y) = (1,0)
      simp [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      all_goals
        ring
    · -- Assume (x,y) = (1,2)
      simp [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      all_goals
        ring
    · -- Assume (x,y) = (0,1)
      simp [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      all_goals
        ring
    · -- Assume (x,y) = (2,1)
      simp [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      all_goals
        ring