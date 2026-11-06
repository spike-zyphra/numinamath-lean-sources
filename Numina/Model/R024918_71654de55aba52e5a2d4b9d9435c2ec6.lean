import Mathlib

theorem algebra_101079 {a b c x y z : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxy : a * x = b * y) (hyz : b * y = c * z)
    (hzz : c * z = a * x) (h : b ^ 2 = a * c) : y ^ 2 = x * z := by
  have eq1 : a * x = c * z := by 
    nlinarith
  
  have eq2 : b * x = c * y := by
    have h1 : a * x = b * y := by linarith
    have h3 : a * x * b = b ^ 2 * y := by
      calc
        a * x * b = (a * x) * b := by ring
        _ = (b * y) * b := by rw [h1]
        _ = b ^ 2 * y := by ring
    have h4 : b ^ 2 = a * c := h
    have h5 : a * x * b = (a * c) * y := by
      rw [h4] at h3
      linarith
    have h6 : x * b = c * y := by
      apply (mul_left_inj' (ne_of_gt ha)).mp
      linarith
    linarith

  have eq4 : (b * x) ^ 2 = (c * y) ^ 2 := by
    rw [eq2]

  have eq5 : b ^ 2 * x ^ 2 = c ^ 2 * y ^ 2 := by
    nlinarith [eq4]

  have eq6 : (a * c) * x ^ 2 = c ^ 2 * y ^ 2 := by
    have h8 : b ^ 2 = a * c := h
    rw [h8] at eq5 
    linarith

  have eq7 : a * x ^ 2 = c * y ^ 2 := by
    nlinarith [eq6, sq_pos_of_pos ha, sq_pos_of_pos hc]

  have eq8 : a * x ^ 2 = c * x * z := by
    have h9 : a * x = c * z := eq1
    have h10 : a * x ^ 2 = (a * x) * x := by ring
    rw [h10]
    rw [h9]
    all_goals ring

  have eq9 : c * x * z = c * y ^ 2 := by
    linarith [eq7, eq8]

  have eq10 : x * z = y ^ 2 := by
    apply (mul_left_inj' (ne_of_gt hc)).mp
    linarith

  linarith [eq10]