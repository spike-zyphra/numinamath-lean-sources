import Mathlib

theorem algebra_3815 {x : ℂ} (hx : x^2 + 2 * x + 4 = 0) :
    2 * x^4 + x^3 - 3 * x^2 - 22 * x + 2023 = 2043 := by
  have h1 : x^2 = -2 * x - 4 := by
    have eq1 : x^2 + 2 * x + 4 = 0 := hx
    calc
      x^2 = (x^2 + 2 * x + 4) - 2 * x - 4 := by ring
      _ = 0 - 2 * x - 4 := by rw [eq1]
      _ = -2 * x - 4 := by ring
  have h2 : x^3 = 8 := by
    calc
      x^3 = x * x^2 := by ring
      _ = x * (-2 * x - 4) := by rw [h1]
      _ = -2 * x^2 - 4 * x := by ring
      _ = -2 * (-2 * x - 4) - 4 * x := by rw [h1]
      _ = 8 := by
        ring_nf
        <;> simp [Complex.ext_iff] at *
        <;> try ring_nf at *
        <;> try tauto
  have h3 : x^4 = 8 * x := by
    calc
      x^4 = (x^2)^2 := by ring
      _ = (-2 * x - 4)^2 := by rw [h1]
      _ = 4 * x^2 + 16 * x + 16 := by ring_nf
      _ = 4 * (-2 * x - 4) + 16 * x + 16 := by rw [h1]
      _ = 8 * x := by
        ring_nf
        <;> simp [Complex.ext_iff] at *
        <;> try ring_nf at *
        <;> try tauto
  rw [show x^4 = 8 * x by exact h3]
  rw [show x^3 = 8 by exact h2]
  rw [show x^2 = -2 * x - 4 by exact h1]
  ring_nf
  <;> simp [Complex.ext_iff, pow_two] at *
  <;> ring_nf
  <;> try tauto