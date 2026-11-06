import Mathlib

theorem algebra_2635 {a b p m: ℝ}(hab : a ≠ 0 ∧ b ≠ 0 ∧ a^2 ≠ b)
  (m_def : m = a * b / (a^2 - b)) :
  p * m^2 / (a * m - b) - p * m / a = p := by
  rcases hab with ⟨ha, hb, hab2⟩
  have m_eq : m = a * b / (a^2 - b) := m_def
  have am_sub_b : a * m - b = b^2 / (a^2 - b) := by
    rw [m_eq]
    have denom_ne_zero : a^2 - b ≠ 0 := by
      intro h
      apply hab2
      linarith
    field_simp [denom_ne_zero, ha, hb]
    <;> ring
  have eq1 : p * m ^ 2 / (a * m - b) = p * a^2 / (a^2 - b) := by
    rw [am_sub_b]
    rw [m_eq]
    have denom_ne_zero : a^2 - b ≠ 0 := by
      intro h
      apply hab2
      linarith
    field_simp [denom_ne_zero, ha, hb]
    <;> ring_nf
  have eq2 : p * m / a = p * b / (a^2 - b) := by
    rw [m_eq]
    have denom_ne_zero : a^2 - b ≠ 0 := by
      intro h
      apply hab2
      linarith
    field_simp [denom_ne_zero, ha, hb]
    <;> ring
  rw [eq1, eq2]
  have denom_ne_zero : a^2 - b ≠ 0 := by
    intro h
    apply hab2
    linarith
  field_simp [denom_ne_zero, ha, hb]
  <;> ring