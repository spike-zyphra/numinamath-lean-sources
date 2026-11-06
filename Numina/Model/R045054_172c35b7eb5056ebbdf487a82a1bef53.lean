import Mathlib

theorem algebra_2138 {x y z : ℝ} (hx : x ≠ -1) (hy : y ≠ -2) (hz : z ≠ -3) (hxy : x / (x + 1) = y / (y + 2)) (hyz : y / (y + 2) = z / (z + 3)) (hzz: z / (z + 3) = (x + y + z) / 3) :
    x + y + z = 0 ∨ x + y + z = -3 := by
  have eq1 : x * (y + 2) = y * (x + 1) := by
    have hx1 : x + 1 ≠ 0 := by
      intro h
      apply hx
      linarith
    have hy1 : y + 2 ≠ 0 := by
      intro h
      apply hy
      linarith
    field_simp [hx1, hy1] at hxy ⊢
    linarith
  have eq2 : y = 2 * x := by
    linarith [eq1]
  have eq3 : y * (z + 3) = z * (y + 2) := by
    have hy1 : y + 2 ≠ 0 := by
      intro h
      apply hy
      linarith
    have hz1 : z + 3 ≠ 0 := by
      intro h
      apply hz
      linarith
    field_simp [hy1, hz1] at hyz ⊢
    linarith
  have eq4 : z = 3 * x := by
    rw [eq2] at eq3
    linarith
  have eq5 : 3 * z = (x + y + z) * (z + 3) := by
    have hz1 : z + 3 ≠ 0 := by
      intro h
      apply hz
      linarith
    field_simp [hz1] at hzz ⊢
    linarith
  rw [eq4] at eq5
  rw [show y = 2 * x by linarith [eq2]] at eq5
  have eq6 : 9 * x * (2 * x + 1) = 0 := by
    nlinarith [eq5]
  cases' (mul_eq_zero.mp eq6) with h1 h2
  · -- Case $9 * x = 0$, so $x = 0$.
    have hx0 : x = 0 := by
      linarith
    have hy0 : y = 0 := by
      linarith [eq2, hx0]
    have hz0 : z = 0 := by
      linarith [eq4, hx0]
    left
    linarith [hx0, hy0, hz0]
  · -- Case $2 * x + 1 = 0$, so $x = -1/2$.
    have hx1 : x = -1 / 2 := by
      linarith
    have hy1 : y = -1 := by
      linarith [eq2, hx1]
    have hz1 : z = -3 / 2 := by
      linarith [eq4, hx1]
    right
    linarith [hx1, hy1, hz1]