import Mathlib

theorem algebra_11979 :
    IsLeast {t : ℝ | ∃ x y, x * y + 1 = 4 * x + y ∧ x > 1 ∧ t = (x + 1) * (y + 2)} 27 := by
  constructor
  · -- Show 27 is in the set
    use 2, 7
    constructor
    · norm_num
    constructor
    · norm_num
    norm_num
  · -- Show 27 is the minimum
    intro t ht
    rcases ht with ⟨x, y, h_eq, hx, heq⟩

    have h_eq2 : y = (4 * x - 1) / (x - 1) := by
      have hx1 : x - 1 ≠ 0 := by linarith
      field_simp
      nlinarith

    have h_subst : t = (6 * x ^ 2 + 3 * x - 3) / (x - 1) := by
      rw [heq]
      rw [h_eq2]
      have hx1 : x - 1 ≠ 0 := by linarith
      field_simp
      ring_nf
      <;> field_simp
      <;> ring_nf
      <;> nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 2)]

    have hx1 : x - 1 > 0 := by linarith
    have h_mul : t ≥ 27 := by
      rw [h_subst]
      apply (le_div_iff₀ (by linarith)).mpr
      -- Multiply original expression by denominator x - 1 (positive).
      nlinarith [sq_nonneg (x - 2)]

    linarith