import Mathlib

theorem number_theory_231549 {x y z : ℕ} (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : x * 16 + y * 175 = z * 205) :
    x * 135 + y * 175 > z * 205 := by
  omega