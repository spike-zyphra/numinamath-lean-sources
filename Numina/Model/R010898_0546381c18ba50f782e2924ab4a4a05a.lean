import Mathlib

theorem algebra_201348 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    x / y + y / x = 66/10 + 538461/9999990 ∧ 1 / x + 1 / y = 1/2 + 769230/9999990 ↔ (x = 13 ∧ y = 2) ∨ (x = 2 ∧ y = 13) := by
  constructor
  · -- Forward implication: If the equations hold, then (x=13,y=2) or (x=2,y=13).
    intro ⟨h1, h2⟩
    have eq3 : x^2 + y^2 = (66 / 10 + 538461 / 9999990) * (x * y) := by
      field_simp [hy, hx] at h1 ⊢
      nlinarith
    have eq4 : x + y = (1/2 + 769230 / 9999990) * (x * y) := by
      field_simp [hy, hx] at h2 ⊢
      nlinarith

    have eq6 : (x - 13) * (x - 2) = 0 := by
      nlinarith [sq_pos_of_ne_zero hx, sq_pos_of_ne_zero hy, sq_nonneg (x - y), sq_nonneg (x + y - 0)]
    cases' (mul_eq_zero.1 eq6) with h7 h8
    · -- Case x = 13
      have hx13 : x = 13 := by linarith
      have hy2 : y = 2 := by
        nlinarith [hx13, h2]
      left
      exact ⟨hx13, hy2⟩
    · -- Case x = 2
      have hx2 : x = 2 := by linarith
      have hy13 : y = 13 := by
        nlinarith [hx2, h2]
      right
      exact ⟨hx2, hy13⟩
  · -- Backward implication: given the solutions, prove the equations.
    rintro (h | h)
    · -- First solution (x = 13, y = 2)
      rw [h.1, h.2]
      constructor <;> norm_num
    · -- Second solution (x = 2, y = 13)
      rw [h.1, h.2]
      constructor <;> norm_num