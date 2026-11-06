import Mathlib

theorem algebra_15143 : IsLeast {w : ℝ | ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    x⁻¹ + y⁻¹ + z⁻¹ = 6 ∧ w = x ^ 3 * y ^ 2 * z} (1 / 108) := by
  constructor
  · -- Show 1/108 is achievable using x = 1/3, y = 1/2, z = 1
    use 1 / 3, 1 / 2, 1
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    all_goals norm_num
  · -- Show 1/108 is the smallest element
    intro w hw
    rcases hw with ⟨x, y, z, hx, hy, hz, h_eq, heq⟩
    have h1 : 0 < x := hx
    have h2 : 0 < y := hy
    have h3 : 0 < z := hz
    have h4 : x⁻¹ + y⁻¹ + z⁻¹ = 6 := h_eq
    have h5 : x ^ 3 * y ^ 2 * z ≥ 1 / 108 := by
      have h31 : y * z + x * z + x * y = 6 * (x * y * z) := by
        field_simp at h_eq ⊢
        nlinarith
      have h70 : (x ^ 3 * y ^ 2 * z) ≥ 1 / 108 := by
        have h40 : y * z + x * z + x * y = 6 * (x * y * z) := h31
        have h90 : (x ^ 3 * y ^ 2 * z) ≥ 1 / 108 := by
          have h40 : y * z + x * z + x * y = 6 * (x * y * z) := h31
          nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (y - 1 / 2), sq_nonneg (z - 1),
            sq_nonneg (x * y - 1 / 6), sq_nonneg (y * z - 1 / 2), sq_nonneg (x * z - 1 / 3),
            mul_pos hx hy, mul_pos hy hz, mul_pos hx hz,
            mul_pos (show 0 < x * y by positivity) (show 0 < x * z by positivity),
            mul_pos (show 0 < x * y by positivity) (show 0 < y * z by positivity),
            mul_pos (show 0 < x * z by positivity) (show 0 < y * z by positivity)]
        linarith
      linarith
    have heq' : w = x ^ 3 * y ^ 2 * z := by linarith [heq]
    linarith [heq', h5]