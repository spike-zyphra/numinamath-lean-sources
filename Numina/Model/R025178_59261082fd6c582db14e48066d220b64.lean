import Mathlib

theorem algebra_119811 {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : (x + y) / z = (y + z) / x) (h2 : (y + z) / x = (z + x) / y) :
    ((x + y) * (y + z) * (z + x)) / (x * y * z) = 8 ∨ ((x + y) * (y + z) * (z + x)) / (x * y * z) = -1 := by

  have eq1 : (x + y) * x = z * (y + z) := by
    field_simp [hx, hz] at h1 ⊢
    linarith
  have eq2 : (y + z) * y = x * (z + x) := by
    field_simp [hx, hy] at h2 ⊢
    linarith

  have eq3 : (x - z) * (x + y + z) = 0 := by
    nlinarith
  have eq4 : (y - x) * (x + y + z) = 0 := by
    nlinarith

  by_cases h : x + y + z = 0
  · -- Assume x + y + z = 0, compute the value
    have h3 : (x + y) * (y + z) * (z + x) = - (x * y * z) := by
      have hx1 : x + y = - z := by
        linarith
      have hy1 : y + z = - x := by
        linarith
      have hz1 : z + x = - y := by
        linarith
      rw [hx1, hy1, hz1]
      ring
    have h4 : ((x + y) * (y + z) * (z + x)) / (x * y * z) = -1 := by
      rw [h3]
      have h5 : x * y * z ≠ 0 := by
        apply mul_ne_zero
        apply mul_ne_zero
        · exact hx
        · exact hy
        · exact hz
      field_simp [h5]
    right
    exact h4
  · -- Assume x + y + z ≠ 0, then equations simplify to variables being equal.
    have eq5 : x - z = 0 := by
      apply (mul_right_inj' h).mp
      linarith
    have eq6 : y - x = 0 := by
      apply (mul_right_inj' h).mp
      linarith
    have hx1 : x = z := by linarith
    have hy1 : y = x := by linarith
    have h_eq : x = y := by linarith
    have h_eq2 : x = z := by linarith
    have hx2 : y = z := by linarith [h_eq, h_eq2]
    have hx3 : (x + y) * (y + z) * (z + x) = 8 * (x * y * z) := by
      rw [show y = x by linarith, show z = x by linarith]
      ring_nf
    have h4 : ((x + y) * (y + z) * (z + x)) / (x * y * z) = 8 := by
      rw [hx3]
      have h5 : x * y * z ≠ 0 := by
        apply mul_ne_zero
        apply mul_ne_zero
        · exact hx
        · exact hy
        · exact hz
      field_simp [h5]
      <;> nlinarith
    left
    exact h4