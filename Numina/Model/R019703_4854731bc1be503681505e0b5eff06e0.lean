import Mathlib

theorem algebra_54487: IsGreatest {z : ℝ | ∃ x y : ℝ, x ≠ 0 ∧ y ≠ 0 ∧ x + 2018 / y = 1000 ∧ 9 / x + y = 1 ∧ z = x + 1000 * y} 1991 := by
  constructor
  · -- Show that 1991 is in the set.
    use -9, 2
    norm_num
  · -- Show that any z in the set is ≤ 1991.
    rintro z ⟨x, y, hx, hy, h1, h2, hz⟩
    have eq1 : x * y + 2018 = 1000 * y := by
      have h1' : y ≠ 0 := hy
      field_simp at h1
      linarith
    have eq2 : 9 + x * y = x := by
      have h2' : x ≠ 0 := hx
      field_simp at h2
      linarith
    have eq3 : 1000 * y ^ 2 - 3009 * y + 2018 = 0 := by
      nlinarith [eq1, eq2]
    have h3 : (y - 2) * (1000 * y - 1009) = 0 := by
      nlinarith [eq3]
    cases' (mul_eq_zero.1 h3) with hy1 hy2
    · -- Case 1: y - 2 = 0, so y = 2.
      have hy2eq : y = 2 := by linarith
      have hx1 : x = -9 := by
        rw [hy2eq] at eq2
        linarith
      linarith [hz, hx1, hy2eq]
    · -- Case 2: 1000 * y - 1009 = 0, so y = 1009/1000.
      have hyy : y = 1009 / 1000 := by
        linarith
      have hx2 : x = -1000 := by
        rw [hyy] at eq2
        linarith
      linarith [hz, hx2, hyy]