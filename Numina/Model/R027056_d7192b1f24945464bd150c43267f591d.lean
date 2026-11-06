import Mathlib

theorem algebra_214799 {a : ℝ} (ha : a ≠ 0) (h : a / 2 - 2 / a = 3) :
    (a^8 - 256) / (16 * a^4) * (2 * a / (a^2 + 4)) = 33 := by
  have h1 : a^2 - 6 * a - 4 = 0 := by 
    have h2 : a ≠ 0 := ha
    field_simp at h
    nlinarith [h]
  have h2 : a^2 = 6 * a + 4 := by linarith

  have h3 : a^3 = 40 * a + 24 := by
    calc
      a ^ 3 = a * a^2 := by ring
      _ = a * (6 * a + 4) := by rw [h2]
      _ = 6 * a^2 + 4 * a := by ring
      _ = 6 * (6 * a + 4) + 4 * a := by rw [h2]
      _ = 40 * a + 24 := by ring

  have h4 : a^4 = 264 * a + 160 := by
    calc
      a ^ 4 = a * a^3 := by ring
      _ = a * (40 * a + 24) := by rw [h3]
      _ = 40 * a^2 + 24 * a := by ring
      _ = 40 * (6 * a + 4) + 24 * a := by rw [h2]
      _ = 264 * a + 160 := by ring

  have h5 : a^8 - 256 = (a^2 - 4) * (a^2 + 4) * (a^4 + 16) := by
    ring
  have ha1 : a^2 + 4 ≠ 0 := by
    by_contra h'
    have h'' : a^2 = -4 := by
      nlinarith
    have h2 : a^2 ≥ 0 := sq_nonneg a
    nlinarith [h2, h'']

  have h6 : a^2 - 4 = 6*a := by
    nlinarith [h2]
  have h7 : a^4 + 16 = 264*a + 176 := by
    have h8 : a^4 = 264*a + 160 := h4
    linarith [h8]

  have h9 : (a^8 - 256) / (16 * a^4) * (2 * a / (a^2 + 4)) =
      ((a^2 - 4) * (a^4 + 16) * (2*a)) / (16 * a^4) := by
    rw [h5]
    field_simp [ha, ha1]
    ring
  rw [h9]

  have h8 : ((a^2 - 4) * (a^4 + 16) * (2*a)) / (16 * a^4) = 33 := by
    rw [h6, h7]
    have h9 : 16 * a^4 ≠ 0 := by
      apply mul_ne_zero
      norm_num
      exact pow_ne_zero 4 ha
    field_simp [h9, ha]
    <;> 
      nlinarith [sq_pos_of_ne_zero ha, h1, sq_nonneg (a^2), sq_nonneg (a^3), sq_nonneg (a^4)]

  exact h8