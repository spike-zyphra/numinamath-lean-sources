import Mathlib

theorem algebra_195034 (x y : ℤ) :
    x^2 + y^2 = x + y + 2 ↔
    (x, y) = (-1, 0) ∨ (x, y) = (-1, 1) ∨ (x, y) = (0, -1) ∨ (x, y) = (0, 2) ∨
    (x, y) = (1, -1) ∨ (x, y) = (1, 2) ∨ (x, y) = (2, 0) ∨ (x, y) = (2, 1) := by
  constructor
  · -- Forward direction: if x^2 + y^2 = x + y + 2, then it is one of the above points.
    rintro H
    have h1 : x ≥ -1 := by nlinarith [sq_nonneg (x + 1), sq_nonneg (y - 2), sq_nonneg (x - 2), sq_nonneg (y + 1)]
    have h2 : x ≤ 2 := by nlinarith [sq_nonneg (x + 1), sq_nonneg (y - 2), sq_nonneg (x - 2), sq_nonneg (y + 1)]
    have h3 : y ≥ -1 := by nlinarith [sq_nonneg (x + 1), sq_nonneg (y - 2), sq_nonneg (x - 2), sq_nonneg (y + 1)]
    have h4 : y ≤ 2 := by nlinarith [sq_nonneg (x + 1), sq_nonneg (y - 2), sq_nonneg (x - 2), sq_nonneg (y + 1)]
    interval_cases x <;> interval_cases y
    <;> norm_num at H ⊢
    <;> tauto
  · -- Backward direction: if it is one of the above points, then x^2 + y^2 = x + y + 2
    rintro (h | h | h | h | h | h | h | h)
    · -- Case (-1, 0)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (-1, 1)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (0, -1)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (0, 2)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (1, -1)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (1, 2)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (2, 0)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Case (2, 1)
      simp [Prod.ext_iff] at h ⊢
      rcases h with ⟨rfl, rfl⟩
      norm_num