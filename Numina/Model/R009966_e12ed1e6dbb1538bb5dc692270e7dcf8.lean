import Mathlib

theorem algebra_13709 (foot yard : ℝ) (hx : foot^3 = 6) (h : yard = 3 * foot) : 5 * yard^3 = 810 := by
  have h1 : yard^3 = 27 * foot^3 := by
    rw [h]
    ring_nf
    <;> nlinarith [sq_nonneg (foot), sq_nonneg (3 * foot)]
  calc
    5 * yard^3 = 5 * (27 * foot^3) := by rw [h1]
    _ = 5 * 27 * foot^3 := by ring
    _ = 135 * foot^3 := by ring
    _ = 135 * 6 := by rw [hx]
    _ = 810 := by norm_num