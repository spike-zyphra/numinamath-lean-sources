import Mathlib

theorem algebra_16140 :
    IsLeast {d : ℝ | ∃ x y z : ℝ, d = x^2 + y^2 + z^2 ∧ x^3 + y^3 + z^3 - 3*x*y*z = 1} 1 := by
  constructor
  · -- We will prove that 1 belongs to the set
    use 1, 0, 0
    norm_num
  · -- We will prove that 1 is the least value
    intro d ⟨x, y, z, h_eq, h_eq1⟩
    have h1 : x^3 + y^3 + z^3 - 3*x*y*z = 1 := h_eq1
    have h2 : (x + y + z) * (x^2 + y^2 + z^2 - (x*y + y*z + z*x)) = 1 := by
      ring_nf at h1 ⊢
      nlinarith
    have h3 : x^2 + y^2 + z^2 - (x*y + y*z + z*x) ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    nlinarith [sq_nonneg (x + y + z - 1), sq_nonneg (x + y + z + 1), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]