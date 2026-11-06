import Mathlib

theorem algebra_325401 (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (h1 : u ≠ 1) (h2 : v ≠ 1) (h3 : w ≠ 1) (h4 : Real.logb u (v * w) + Real.logb v w = 5)
    (h5 : Real.logb v u + Real.logb w v = 3) :
    Real.logb w u = 4 / 5 := by

  have h6 : Real.logb u (v * w) = (Real.log (v * w) ) / Real.log u := by
    field_simp [Real.logb]

  have h7 : Real.log (v * w) = Real.log v + Real.log w := by
    rw [Real.log_mul (by linarith) (by linarith)]

  have h8 : Real.logb v w = Real.log w / Real.log v := by
    field_simp [Real.logb]

  have eq1 : (Real.log v + Real.log w) / Real.log u + Real.log w / Real.log v = 5 := by
    rw [h6, h7, h8] at h4
    linarith

  have h9 : Real.logb v u = Real.log u / Real.log v := by
    field_simp [Real.logb]

  have h10 : Real.logb w v = Real.log v / Real.log w := by
    field_simp [Real.logb]

  have eq2 : Real.log u / Real.log v + Real.log v / Real.log w = 3 := by
    rw [h9, h10] at h5
    linarith

  have hu1 : Real.log u ≠ 0 := by
    have h1' : u ≠ 1 := h1
    exact Real.log_ne_zero_of_pos_of_ne_one hu h1'

  have hv1 : Real.log v ≠ 0 := by
    have h2' : v ≠ 1 := h2
    exact Real.log_ne_zero_of_pos_of_ne_one hv h2'

  have hw1 : Real.log w ≠ 0 := by
    have h3' : w ≠ 1 := h3
    exact Real.log_ne_zero_of_pos_of_ne_one hw h3'

  have eq3 : (Real.log v + Real.log w) * Real.log v + Real.log w * Real.log u = 5 * (Real.log u * Real.log v) := by
    have h11 : Real.log v ≠ 0 := hv1
    have h12 : Real.log u ≠ 0 := hu1
    field_simp [h11, h12] at eq1 ⊢
    nlinarith [eq1]

  have eq4 : Real.log u * Real.log w + (Real.log v) ^ 2 = 3 * (Real.log v * Real.log w) := by
    have h13 : Real.log v ≠ 0 := hv1
    have h14 : Real.log w ≠ 0 := hw1
    field_simp [h13, h14] at eq2 ⊢
    nlinarith [eq2]

  have eq5 : 5 * Real.log u = 4 * Real.log w := by
    have eq6 : 4 * (Real.log v) * (Real.log w) = 5 * (Real.log u) * (Real.log v) := by
      nlinarith [sq_pos_of_ne_zero (show Real.log v ≠ 0 by exact hv1)]
    have h15 : Real.log v ≠ 0 := hv1
    have eq7 : 4 * Real.log w = 5 * Real.log u := by
      apply (mul_left_inj' h15).mp
      linarith
    linarith [eq7]

  have eq6 : Real.logb w u = Real.log u / Real.log w := by
    field_simp [Real.logb]

  rw [eq6]
  have hw1' : Real.log w ≠ 0 := hw1
  field_simp [hw1']
  <;> nlinarith [eq5]