import Mathlib

theorem algebra_2271 :
    IsLeast {z : ℚ | ∃ x y : ℚ, z = 5 * x ^ 2 + 4 * y ^ 2 - 8 * x * y + 2 * x + 4} 3 := by
  constructor
  · -- Show that 3 is achievable at (-1, -1)
    use -1, -1
    norm_num
  · -- Show 3 is a lower bound
    intro z hz
    rcases hz with ⟨x, y, h_eq⟩
    have h1 : z = 5 * (x + 1)^2 + 4 * (y + 1)^2 - 8 * (x + 1) * (y + 1) + 3 := by
      rw [h_eq]
      ring_nf
    have h2 : z ≥ 3 := by
      nlinarith [sq_nonneg (5 * (x + 1) - 4 * (y + 1)), sq_nonneg (y + 1), sq_nonneg (x + 1)]
    linarith