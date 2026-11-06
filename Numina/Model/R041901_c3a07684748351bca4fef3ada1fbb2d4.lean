import Mathlib

theorem algebra_285598 (x y z t : ℝ) (hx : x ≠ y) (hy : y ≠ z) (hz : z ≠ t) 
    (hxz : x ≠ z) (hyt : y ≠ t) (hdenom : x - y + z - t ≠ 0) :
    ((x^2 - y^2)^3 + (y^2 - z^2)^3 + (z^2 - t^2)^3 + (t^2 - x^2)^3) /
    ((x - y)^3 + (y - z)^3 + (z - t)^3 + (t - x)^3) =
    ((x + z) * (y + t) * (x^2 - y^2 + z^2 - t^2)) / (x - y + z - t) := by
  have h1 : (x - y)^3 + (y - z)^3 + (z - t)^3 + (t - x)^3 ≠ 0 := by
    have h2 : (x - y) + (y - z) + (z - t) + (t - x) = 0 := by
      ring
    have h3 : (x - y)^3 + (y - z)^3 + (z - t)^3 + (t - x)^3 =
        3 * ((x - y) * (y - z) * (z - t) + (x - y) * (y - z) * (t - x) + (x - y) * (z - t) * (t - x) + (y - z) * (z - t) * (t - x)) := by 
      ring
    have h4 : 3 * ((x - y) * (y - z) * (z - t) + (x - y) * (y - z) * (t - x) + (x - y) * (z - t) * (t - x) + (y - z) * (z - t) * (t - x)) ≠ 0 := by 
      by_contra h5
      have h6 : (x - y) * (y - z) * (z - t) + (x - y) * (y - z) * (t - x) + (x - y) * (z - t) * (t - x) + (y - z) * (z - t) * (t - x) = 0 := by
        linarith
      have h7 : (z - x) * ((x - y) * (y - z) - (z - t) * (t - x)) = 0 := by 
        nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne hx), sq_pos_of_ne_zero (sub_ne_zero_of_ne hy), 
          sq_pos_of_ne_zero (sub_ne_zero_of_ne hz), sq_pos_of_ne_zero (sub_ne_zero_of_ne hxz), sq_pos_of_ne_zero (sub_ne_zero_of_ne hyt)
        ]
      cases' (mul_eq_zero.mp h7) with h8 h9
      · -- Case h8 : z - x = 0
        have h9 : x = z := by linarith
        exfalso
        apply hxz
        linarith
      · -- Case h9 : (x - y) * (y - z) - (z - t) * (t - x) = 0
        have h10 : (x - y + z - t) * (y - t) = 0 := by 
          nlinarith
        cases' (mul_eq_zero.mp h10) with h11 h12
        · -- Case h11 : x - y + z - t = 0
          exfalso
          apply hdenom
          linarith
        · -- Case h12 : y - t = 0
          exfalso
          apply hyt
          linarith
    intro h
    rw [h3] at h 
    apply h4
    linarith
  field_simp [h1, hdenom]
  ring_nf