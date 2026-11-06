import Mathlib

theorem algebra_198167 : 
    {(x, y) : ℝ × ℝ | x^2 - x * y + y^2 = 49 * (x - y) ∧ x^2 + x * y + y^2 = 76 * (x + y) } = ({(0, 0), (40, -24)} : Set <| ℝ × ℝ) := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x, y) satisfies both equations, prove it's in {(0, 0), (40, -24)}
    rintro ⟨h₁, h₂⟩
    have h3 : (x - 40) * (x - 0) = 0 := by
      nlinarith [sq_nonneg (x - 40), sq_nonneg (y + 24), sq_nonneg (x - y), sq_nonneg (x + y - 41)]
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- Case x - 40 = 0
      have h6 : x = 40 := by
        linarith
      have h7 : y = -24 := by
        nlinarith [h6, sq_nonneg (y + 24), sq_nonneg (x - 40)]
      simp [h6, h7]
    · -- Case x = 0
      have h8 : x = 0 := by
        linarith
      have h9 : y = 0 := by
        nlinarith [h8, sq_nonneg (y), sq_nonneg (x)]
      simp [h8, h9]
  · -- Show that (0,0) and (40,-24) satisfy both equations.
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Check (0,0)
      constructor <;> norm_num
    · -- Check (40,-24)
      constructor <;> norm_num