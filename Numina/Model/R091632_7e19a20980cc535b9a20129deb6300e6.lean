import Mathlib

theorem algebra_100380 (x y z w v u : ℝ)
    (h1 : z = x + y) (h2 : w = y + z) (h3 : v = z + w)
    (h4 : u = w + v) (h5 : v = 10) :
    x + y + z + w + v + u = 40 := by
  have hw : w = x + 2 * y := by
    rw [h1] at h2
    linarith

  have hv : v = 2 * x + 3 * y := by
    rw [show z = x + y by linarith, hw] at h3
    linarith

  have h_eq : 2 * x + 3 * y = 10 := by linarith [h5, hv]

  have hu : u = 3 * x + 5 * y := by
    rw [h4, hw, hv]
    linarith

  have total : x + y + z + w + v + u = 8 * x + 12 * y := by
    rw [h1, hw, hv, hu]
    linarith

  calc
    x + y + z + w + v + u = 8 * x + 12 * y := by linarith [total]
    _ = 4 * (2 * x + 3 * y) := by ring
    _ = 4 * 10 := by
      rw [h_eq]
    _ = 40 := by norm_num