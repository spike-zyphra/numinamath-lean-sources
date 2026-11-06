import Mathlib

theorem algebra_241179 (x y : ℝ) :
    (5 * x ^ 2 - 14 * x * y + 10 * y ^ 2 = 17 ∧ 4 * x ^ 2 - 10 * x * y + 6 * y ^ 2 = 8) ↔
    (x = -1 ∧ y = -2) ∨ (x = 11 ∧ y = 7) ∨ (x = -11 ∧ y = -7) ∨ (x = 1 ∧ y = 2) := by
  constructor
  · -- First direction: if (x, y) satisfies the system, then it is one of the four solutions
    rintro ⟨h₁, h₂⟩
    have h3 : (x - 2 * y)^2 = 9 := by
      nlinarith
    have h4 : x - 2 * y = 3 ∨ x - 2 * y = -3 := by
      have h5 : (x - 2 * y)^2 - 9 = 0 := by linarith
      have h6 : (x - 2 * y - 3) * (x - 2 * y + 3) = 0 := by
        linarith
      cases' (mul_eq_zero.mp h6) with h7 h8
      · -- Case where \(x - 2y - 3 = 0\), which is \(x - 2y = 3\)
        left
        linarith
      · -- Case where \(x - 2y + 3 = 0\), which is \(x - 2y = -3\)
        right
        linarith
    cases h4 with
    | inl h5 =>
      have hx : x = 2 * y + 3 := by linarith
      rw [hx] at h₂
      have h : (y + 7) * (y + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h) with hy1 hy2
      · -- Case where \(y = -7\)
        have hy : y = -7 := by linarith
        have hx : x = -11 := by
          linarith [hx, hy]
        have h8 : (x = -11 ∧ y = -7) := ⟨hx, hy⟩
        simp [h8]
      · -- Case where \(y = -2\)
        have hy : y = -2 := by linarith
        have hx : x = -1 := by
          linarith [hx, hy]
        have h8 : (x = -1 ∧ y = -2) := ⟨hx, hy⟩
        simp [h8]
    | inr h6 =>
      have hx : x = 2 * y - 3 := by linarith
      rw [hx] at h₂
      have h : (y - 7) * (y - 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h) with hy1 hy2
      · -- Case where \(y = 7\)
        have hy : y = 7 := by linarith
        have hx : x = 11 := by
          linarith [hx, hy]
        have h8 : (x = 11 ∧ y = 7) := ⟨hx, hy⟩
        simp [h8]
      · -- Case where \(y = 2\)
        have hy : y = 2 := by linarith
        have hx : x = 1 := by
          linarith [hx, hy]
        have h8 : (x = 1 ∧ y = 2) := ⟨hx, hy⟩
        simp [h8]
  · -- Second direction: the four solutions satisfy the system
    rintro (h | h | h | h)
    · -- (-1, -2)
      rcases h with ⟨rfl, rfl⟩
      constructor <;> norm_num
    · -- (11, 7)
      rcases h with ⟨rfl, rfl⟩
      constructor <;> norm_num
    · -- (-11, -7)
      rcases h with ⟨rfl, rfl⟩
      constructor <;> norm_num
    · -- (1, 2)
      rcases h with ⟨rfl, rfl⟩
      constructor <;> norm_num