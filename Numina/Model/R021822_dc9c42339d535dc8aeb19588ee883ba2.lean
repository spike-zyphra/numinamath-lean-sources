import Mathlib

theorem algebra_292714 {a b : ℝ} (ha : a ≠ 1) (hb : b ≠ 1)
    (h : 2 * b = 1 + a * b) :
    (a + 1) / (a - 1) - (b + 1) / (b - 1) = 2 := by
  have h1 : a - 1 ≠ 0 := by
    intro h11
    apply ha
    linarith

  have h2 : b - 1 ≠ 0 := by
    intro h22
    apply hb
    linarith

  have h3 : (a + 1) / (a - 1) - (b + 1) / (b - 1) =
      ((a + 1) * (b - 1) - (b + 1) * (a - 1)) / ((a - 1) * (b - 1)) := by
    field_simp [h1, h2]
    <;> ring
  rw [h3]

  have h4 : ((a + 1) * (b - 1) - (b + 1) * (a - 1)) = 2 * (b - a) := by
    nlinarith

  have h5 : (a - 1) * (b - 1) = b - a := by
    have h6 : a * b = 2 * b - 1 := by linarith
    nlinarith

  have h5' : (a - 1) * (b - 1) ≠ 0 := by
    apply mul_ne_zero
    · exact h1
    · exact h2

  have h6 : ((a + 1) * (b - 1) - (b + 1) * (a - 1)) = 2 * ((a - 1) * (b - 1)) := by
    nlinarith [h4, h5]

  rw [h6]
  field_simp [h5', h1, h2]
  <;> nlinarith