import Mathlib

theorem algebra_240877 (x y : ℝ) :
    (26*x^2+42*x*y+17*y^2=10 ∧ 10*x^2+18*x*y+8*y^2=6) ↔
    (x=-1 ∧ y=2) ∨ (x=-11 ∧ y=14) ∨ (x=11 ∧ y=-14) ∨ (x=1 ∧ y=-2) := by
  constructor
  · -- Forward direction: if system holds, then solutions
    rintro ⟨h₁, h₂⟩
    have h3 : (x + 1) * (x + 11) * (x - 11) * (x - 1) = 0 := by
      nlinarith [sq_nonneg (x * y), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (y + 2), sq_nonneg (y - 2)]
    cases' (mul_eq_zero.mp h3) with h4 h5
    cases' (mul_eq_zero.mp h4) with h6 h7
    cases' (mul_eq_zero.mp h6) with h8 h9
    · -- Case x + 1 = 0
      have hx : x = -1 := by linarith
      have hy : y = 2 := by
        rw [hx] at h₁
        nlinarith
      left
      exact ⟨hx, hy⟩
    · -- Case x + 11 = 0
      have hx : x = -11 := by linarith
      have hy : y = 14 := by
        rw [hx] at h₁
        nlinarith
      right
      left
      exact ⟨hx, hy⟩
    · -- Case x - 11 = 0
      have hx : x = 11 := by linarith
      have hy : y = -14 := by
        rw [hx] at h₁
        nlinarith
      right
      right
      left
      exact ⟨hx, hy⟩
    · -- Case x - 1 = 0
      have hx : x = 1 := by linarith
      have hy : y = -2 := by
        rw [hx] at h₁
        nlinarith
      right
      right
      right
      exact ⟨hx, hy⟩
  · -- Backward direction
    rintro (h | h | h | h)
    · -- Case (-1, 2)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · norm_num
      · norm_num
    · -- Case (-11, 14)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · norm_num
      · norm_num
    · -- Case (11, -14)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · norm_num
      · norm_num
    · -- Case (1, -2)
      rcases h with ⟨rfl, rfl⟩
      constructor
      · norm_num
      · norm_num