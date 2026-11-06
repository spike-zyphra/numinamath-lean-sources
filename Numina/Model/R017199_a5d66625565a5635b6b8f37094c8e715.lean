import Mathlib

theorem algebra_287153 {a b : ℝ} (ha : a ≠ -1) (hb : b ≠ 1)
    (h : a + 1 / (a + 1) = b + 1 / (b - 1) - 2) (h' : a - b + 2 ≠ 0) :
    a * b - a + b = 2 := by
  have h1 : a + 1 ≠ 0 := by
    intro h2
    apply ha
    linarith
  have h2 : b - 1 ≠ 0 := by
    intro h3
    apply hb
    linarith

  have eq1 : (a + 1 / (a + 1)) * ((a + 1) * (b - 1)) = (b + 1 / (b - 1) - 2) * ((a + 1) * (b - 1)) := by
    rw [h]

  have eq2 : (a + 1 / (a + 1)) * ((a + 1) * (b - 1)) = a * (a + 1) * (b - 1) + (b - 1) := by
    field_simp [h1]
    <;> ring

  have eq3 : (b + 1 / (b - 1) - 2) * ((a + 1) * (b - 1)) = b * (a + 1) * (b - 1) + (a + 1) - 2 * (a + 1) * (b - 1) := by
    field_simp [h2]
    <;> ring
  rw [eq2, eq3] at eq1
  have eq4 : (a - b + 2) * ((a + 1) * (b - 1) - 1) = 0 := by
    nlinarith
    <;> ring_nf <;> nlinarith
  cases (mul_eq_zero.mp eq4) with
  | inl h3 =>
    exfalso
    have h4 : a - b + 2 = 0 := by
      linarith
    contradiction
  | inr h3 =>
    have h4 : (a + 1) * (b - 1) = 1 := by
      linarith
    nlinarith