import Mathlib

theorem algebra_20368 :
    IsGreatest {m : ℝ | ∃x y z : ℝ, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ x + y + z = 0 ∧ m = (x * y + y * z + z * x) / (x ^ 2 + y ^ 2 + z ^ 2)} (-1 / 2) := by
  constructor
  · -- Show that -1/2 is in the set.
    use 1, -1, 0
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that -1/2 is greatest in the set.
    intro m hm
    rcases hm with ⟨x, y, z, h1, h2, h3, h4, h5⟩
    have h6 : x^2 + y^2 + z^2 ≠ 0 := by
      by_contra h
      have hx1 : x ^ 2 ≥ 0 := by nlinarith
      have hy1 : y ^ 2 ≥ 0 := by nlinarith
      have hz1 : z ^ 2 ≥ 0 := by nlinarith
      have hx2 : x ^ 2 = 0 := by nlinarith
      have hy2 : y ^ 2 = 0 := by nlinarith
      have hz2 : z ^ 2 = 0 := by nlinarith
      have hx3 : x = 0 := by nlinarith
      have hy3 : y = 0 := by nlinarith
      have hz3 : z = 0 := by nlinarith
      exfalso
      apply h1
      linarith
    have h7 : x^2 + y^2 + z^2 = -2 * (x * y + y * z + z * x) := by
      have h : (x + y + z) ^ 2 = 0 := by
        rw [show (x + y + z) = 0 by linarith]
        all_goals norm_num
      nlinarith
    have h8 : (x * y + y * z + z * x) / (x ^ 2 + y ^ 2 + z ^ 2) = -1 / 2 := by
      have h9 : (x * y + y * z + z * x) = -1 / 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by
        nlinarith
      rw [h9]
      field_simp [h6]
      <;> nlinarith 
    linarith [h5, h8]