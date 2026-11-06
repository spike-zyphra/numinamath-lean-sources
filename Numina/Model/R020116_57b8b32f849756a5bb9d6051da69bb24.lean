import Mathlib

theorem algebra_319643 {m : ℝ} (h : ∃! x, (m + 2) * x ^ 2 - 2 * (m + 1) * x + m = 0) :
    ∃! x, (m + 1) * x ^ 2 - 2 * m * x + m - 2 = 0 := by
  rcases h with ⟨x, ⟨hx1, hx2⟩⟩
  by_cases h5 : m + 2 = 0
  · -- m + 2 = 0, so m = -2
    have hm : m = -2 := by linarith
    use 2
    constructor
    · -- Show that 2 is a root
      rw [hm]
      norm_num
    · -- Show that any root is 2
      intro y hy
      rw [hm] at hy
      have h_eq : (-2 + 1) * y ^ 2 - 2 * (-2) * y + (-2) - 2 = 0 := by linarith
      have : (y - 2) ^ 2 = 0 := by nlinarith
      have : y - 2 = 0 := by
        apply pow_eq_zero 
        exact this
      linarith
  · -- m + 2 ≠ 0
    have h3 := hx2 1 (by
      ring_nf
    )
    have hx1' : x = 1 := by
      nlinarith
    have h4 := hx2 (m / (m + 2)) (by
      field_simp [show m + 2 ≠ 0 by assumption]
      <;> nlinarith
    )
    rw [hx1'] at h4
    have : m / (m + 2) = 1 := by linarith
    have : m = m + 2 := by
      field_simp [show m + 2 ≠ 0 by assumption] at this ⊢
      <;> nlinarith
    linarith