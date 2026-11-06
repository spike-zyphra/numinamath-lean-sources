import Mathlib

theorem algebra_12521 {x y x' y': ℝ} (hx : x = 1.2 * y) (hy : y ≠ 0) (hx' : x' ≠ 0)
    (h : x' = y' * 0.9) :
    (x' / x) / (y' / y) = 3 / 4 := by

  have h1 : x ≠ 0 := by
    intro h2
    have h3 : y = 0 := by
      calc
        y = (x) / 1.2 := by
          rw [hx]
          ring_nf
        _ = 0 := by
          rw [h2]
          norm_num
    have h4 : y = 0 := h3
    contradiction

  have h2 : y' ≠ 0 := by
    by_contra h3
    have h4 : x' = 0 := by
      rw [h]
      rw [h3]
      norm_num
    have h5 : x' = 0 := h4
    contradiction

  have eq1 : (x' / x) / (y' / y) = (x' * y) / (x * y') := by 
    field_simp [show x ≠ 0 by assumption, show y ≠ 0 by assumption, show y' ≠ 0 by assumption]
    <;> ring_nf

  rw [eq1]

  rw [h] -- Substitute x' in the numerator
  rw [hx] -- Substitute x in the denominator

  have h3 : y * y' ≠ 0 := by 
    apply mul_ne_zero
    exact hy
    exact h2

  field_simp [show y * y' ≠ 0 by assumption, show y ≠ 0 by assumption, show y' ≠ 0 by assumption]
  <;> ring_nf
  <;> norm_num