import Mathlib

theorem algebra_14491 {x y z : ℕ} (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (hsum : x + y + z = 72) (hrat : x * 3 = y * 1 ∧ y * 4 = z * 3) :
    x = 9 := by
  have h1 : x * 3 = y * 1 := hrat.1
  have h2 : y * 4 = z * 3 := hrat.2
  have hy_eq : y = 3 * x := by
    omega
  have hz_eq : z = 4 * x := by
    rw [hy_eq] at h2
    omega
  rw [hy_eq, hz_eq] at hsum
  omega