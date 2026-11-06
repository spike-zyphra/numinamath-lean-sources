import Mathlib

theorem algebra_327113 (x y : ℤ) :
    x^2 + 2 * x * y + 3 * y^2 - 2 * x + y + 1 = 0 ↔
    (x = 1 ∧ y = 0) ∨ (x = 1 ∧ y = -1) ∨ (x = 3 ∧ y = -1) := by
  constructor
  · -- Forward direction: if the equation holds, then prove the possible solutions
    intro h
    have h1 : x^2 + 2 * x * y + 3 * y^2 - 2 * x + y + 1 = 0 := h
    have eq1 : (x + y - 1) ^ 2 + 2 * y ^ 2 + 3 * y = 0 := by 
      nlinarith 
    have h2 : y ≤ 0 := by 
      nlinarith [sq_nonneg (x + y - 1), sq_nonneg (y)]
    have : y = 0 ∨ y = -1 ∨ y = -2 ∨ y ≤ -3 := by omega
    rcases this with (rfl | rfl | rfl | h3)
    · -- Case y = 0:
      have : x = 1 := by
        nlinarith
      left
      exact ⟨this, rfl⟩
    · -- Case y = -1:
      have : x = 1 ∨ x = 3 := by
        have h_eq : x^2 - 4 * x + 3 = 0 := by 
          nlinarith
        have factored : (x - 1) * (x - 3) = 0 := by
          nlinarith [h_eq]
        cases' (mul_eq_zero.mp factored) with h4 h5
        · left
          linarith
        · right
          linarith
      cases this with
      | inl h =>
        right
        left
        exact ⟨h, rfl⟩
      | inr h =>
        right
        right
        exact ⟨h, rfl⟩
    · -- Case y = -2:
      exfalso
      nlinarith [sq_nonneg (x - 3)]
    · -- Case y ≤ -3:
      exfalso
      nlinarith [sq_nonneg (x + y - 1), sq_nonneg (y + 1), sq_nonneg (x - 3), sq_nonneg (x - 1)]
  · -- Backward direction: possible solutions prove the equation
    rintro (h | h | h)
    · -- Case (1, 0):
      rw [h.1, h.2]
      norm_num
    · -- Case (1, -1):
      rw [h.1, h.2]
      norm_num
    · -- Case (3, -1):
      rw [h.1, h.2]
      norm_num