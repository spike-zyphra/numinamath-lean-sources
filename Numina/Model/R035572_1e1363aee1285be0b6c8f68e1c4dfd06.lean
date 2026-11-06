import Mathlib

theorem algebra_241074 (x y : ℝ) :
    (5 * x ^ 2 + 14 * x * y + 10 * y ^ 2 = 17 ∧ 4 * x ^ 2 + 10 * x * y + 6 * y ^ 2 = 8) ↔
    (x = -1 ∧ y = 2) ∨ (x = 11 ∧ y = -7) ∨ (x = -11 ∧ y = 7) ∨ (x = 1 ∧ y = -2) := by
  constructor
  · -- Assume the conjunction of the two equations, prove the four possible solutions
    rintro ⟨h1, h2⟩
    have h3 : (x + 2 * y) ^ 2 = 9 := by
      nlinarith
    have h4 : x + 2 * y = 3 ∨ x + 2 * y = -3 := by
      have h5 : (x + 2 * y) ^ 2 - 9 = 0 := by linarith
      have h6 : (x + 2 * y - 3) * (x + 2 * y + 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h6) with h7 h8
      · -- Case where x + 2y - 3 = 0
        left
        linarith
      · -- Case where x + 2y + 3 = 0
        right
        linarith
    cases h4 with
    | inl h_eq =>
      have hx : x = 3 - 2 * y := by linarith
      rw [hx] at h2
      have h5 : (y - 7) * (y - 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h5) with h6 h7
      · -- Case where y = 7
        have hy7 : y = 7 := by linarith
        have hx7 : x = -11 := by
          linarith [h_eq, hy7]
        simp [hx7, hy7]
      · -- Case where y = 2
        have hy2 : y = 2 := by linarith
        have hx1 : x = -1 := by
          linarith [h_eq, hy2]
        left
        simp [hx1, hy2]
    | inr h_eq =>
      have hx : x = -3 - 2 * y := by linarith
      rw [hx] at h2
      have h5 : (y + 7) * (y + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h5) with h6 h7
      · -- Case where y = -7
        have hy7 : y = -7 := by linarith
        have hx11 : x = 11 := by
          linarith [h_eq, hy7]
        right
        left
        simp [hx11, hy7]
      · -- Case where y = -2
        have hy2 : y = -2 := by linarith
        have hx1 : x = 1 := by
          linarith [h_eq, hy2]
        right
        simp [hx1, hy2]
  · -- Now prove the reverse direction, that the four solutions satisfy both equations.
    rintro (h | h | h | h)
    · -- (-1, 2)
      rcases h with ⟨rfl, rfl⟩
      constructor <;> norm_num
    · -- (11, -7)
      rcases h with ⟨rfl, rfl⟩
      constructor <;> norm_num
    · -- (-11, 7)
      rcases h with ⟨rfl, rfl⟩
      constructor <;> norm_num
    · -- (1, -2)
      rcases h with ⟨rfl, rfl⟩
      constructor <;> norm_num