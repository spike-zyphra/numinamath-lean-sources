import Mathlib

theorem algebra_233040 (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hne1 : u ≠ 1 ∧ v ≠ 1 ∧ w ≠ 1) (hlog1 : Real.logb u (v * w) + Real.logb v w = 5)
    (hlog2 : Real.logb v u + Real.logb w v = 3) :
    Real.logb w u = 4 / 5 := by
  have hu1 : u ≠ 1 := hne1.1
  have hv1 : v ≠ 1 := hne1.2.1
  have hw1 : w ≠ 1 := hne1.2.2
  have eq1 : Real.logb u (v * w) = (Real.log v + Real.log w) / Real.log u := by
    have eq3 : Real.logb u (v * w) = (Real.log (v * w) ) / Real.log u := by
      field_simp [Real.logb]
    have eq4 : Real.log (v * w) = Real.log v + Real.log w := by 
      rw [Real.log_mul (by linarith) (by linarith)]
    rw [eq4] at eq3
    linarith
  have eq2 : Real.logb v w = Real.log w / Real.log v := by
    field_simp [Real.logb]
  have h10 : Real.logb u (v * w) + Real.logb v w = 5 := by
    linarith [hlog1]
  have eq5 : (Real.log v + Real.log w) / Real.log u + Real.log w / Real.log v = 5 := by 
    rw [eq1, eq2] at h10 
    linarith
  -- rewrite the second equation 
  have eq6 : Real.logb v u = Real.log u / Real.log v := by 
    field_simp [Real.logb]
  have eq3 : Real.logb w v = Real.log v / Real.log w := by 
    field_simp [Real.logb]
  have h11 : Real.logb v u + Real.logb w v = 3 := by 
    linarith [hlog2]
  have eq8 : Real.log u / Real.log v + Real.logb w v = 3 := by 
    rw [eq6] at h11
    linarith
  have eq9 : Real.log u / Real.log v + Real.log v / Real.log w = 3 := by 
    rw [eq3] at eq8 
    linarith
  -- prove logarithm non-zero
  have h7 : Real.log u ≠ 0 := by 
    have h17 : u > 0 := by linarith 
    have h18 : u ≠ 1 := by tauto 
    exact Real.log_ne_zero_of_pos_of_ne_one h17 h18
  have h8 : Real.log v ≠ 0 := by 
    have h17 : v > 0 := by linarith 
    have h18 : v ≠ 1 := by tauto 
    exact Real.log_ne_zero_of_pos_of_ne_one h17 h18
  have h9 : Real.log w ≠ 0 := by 
    have h17 : w > 0 := by linarith 
    have h18 : w ≠ 1 := by tauto 
    exact Real.log_ne_zero_of_pos_of_ne_one h17 h18
  -- convert eq5 and eq9 to linear equations
  have eq10 : (Real.log v + Real.log w) * Real.log v + Real.log w * Real.log u = 5 * Real.log u * Real.log v := by 
    have h9' : Real.log u ≠ 0 := h7
    have h10' : Real.log v ≠ 0 := h8
    field_simp [h9', h10'] at eq5 ⊢ 
    nlinarith
  have eq11 : Real.log u * Real.log w + Real.log v ^ 2 = 3 * Real.log v * Real.log w := by 
    have h9' : Real.log v ≠ 0 := h8 
    have h11' : Real.log w ≠ 0 := h9 
    field_simp [h9', h11'] at eq9 ⊢ 
    nlinarith
  -- solve the system 
  have eq3 : Real.log v * Real.log w = (5 * Real.log u - 3 * Real.log w) * Real.log v := by 
    nlinarith
  have eq4 : Real.log w = 5 * Real.log u - 3 * Real.log w := by 
    apply (mul_left_inj' h8).mp 
    linarith
  have eq5 : 4 * Real.log w = 5 * Real.log u := by 
    linarith
  -- conclude
  have eq6 : Real.log u / Real.log w = 4 / 5 := by 
    have eq7 : Real.log w ≠ 0 := h9 
    field_simp [eq7]
    linarith [eq5]
  have h5' : Real.logb w u = Real.log u / Real.log w := by 
    field_simp [Real.logb]
  rw [h5']
  linarith [eq6]