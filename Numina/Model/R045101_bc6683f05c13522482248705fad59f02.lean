import Mathlib

theorem algebra_946 {x y z k : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : x * y + y * z + z * x = k) (h2 : (x + y) * (y + z) * (z + x) ≠ 0) :
    (x ^ 2 + y ^ 2 + 2 * k) / (x + y) + (y ^ 2 + z ^ 2 + 2 * k) / (y + z) +
    (z ^ 2 + x ^ 2 + 2 * k) / (z + x) =
    4 * (x + y + z) ∧ (x > 0 → y > 0 → z > 0 →
    1 / (x + y) + 1 / (y + z) + 1 / (z + x) ≤ 3 * (x + y + z) / (2 * (x * y + y * z + z * x))) := by
  constructor
  · 
    have h11 : x + y ≠ 0 := by 
      by_contra h
      have h12 : (x + y) * (y + z) * (z + x) = 0 := by 
        rw [h]
        norm_num 
      contradiction 
    have h12 : y + z ≠ 0 := by 
      by_contra h
      have h13 : (x + y) * (y + z) * (z + x) = 0 := by 
        rw [h]
        norm_num 
      contradiction 
    have h13 : z + x ≠ 0 := by 
      by_contra h
      have h14 : (x + y) * (y + z) * (z + x) = 0 := by 
        rw [h]
        norm_num 
      contradiction 
    have eq1 : (x ^ 2 + y ^ 2 + 2 * k) / (x + y) = x + y + 2 * z := by 
      have h14 : x + y ≠ 0 := h11 
      have hk1 : k = x * y + y * z + z * x := by linarith
      rw [hk1] 
      field_simp [(show x + y ≠ 0 by assumption)]
      ring
    have eq2 : (y ^ 2 + z ^ 2 + 2 * k) / (y + z) = y + z + 2 * x := by 
      have h15 : y + z ≠ 0 := h12 
      have hk1 : k = x * y + y * z + z * x := by linarith
      rw [hk1] 
      field_simp [(show y + z ≠ 0 by assumption)]
      ring
    have eq3 : (z ^ 2 + x ^ 2 + 2 * k) / (z + x) = z + x + 2 * y := by 
      have h16 : z + x ≠ 0 := h13 
      have hk1 : k = x * y + y * z + z * x := by linarith
      rw [hk1] 
      field_simp [(show z + x ≠ 0 by assumption)]
      ring
    rw [eq1, eq2, eq3]
    ring
  · 
    intro hx1 hy1 hz1
    have h3 : 0 < (x + y) * (y + z) * (z + x) := by 
      have hx2 : x + y ≠ 0 := by 
        by_contra h
        have h12 : (x + y) * (y + z) * (z + x) = 0 := by 
          rw [h]
          norm_num 
        contradiction 
      have hy2 : y + z ≠ 0 := by 
        by_contra h
        have h13 : (x + y) * (y + z) * (z + x) = 0 := by 
          rw [h]
          norm_num 
        contradiction 
      have hz2 : z + x ≠ 0 := by 
        by_contra h
        have h14 : (x + y) * (y + z) * (z + x) = 0 := by 
          rw [h]
          norm_num 
        contradiction 
      have hx3 : x + y > 0 := by 
        have h21 : x > 0 := by linarith 
        have h22 : y > 0 := by linarith 
        nlinarith 
      have hy3 : y + z > 0 := by 
        have h21 : y > 0 := by linarith 
        have h22 : z > 0 := by linarith
        nlinarith 
      have hz3 : z + x > 0 := by 
        have h21 : z > 0 := by linarith 
        have h22 : x > 0 := by linarith 
        nlinarith 
      positivity
    have h4 : x * y + y * z + z * x > 0 := by 
      have hx2 : x > 0 := hx1
      have hy2 : y > 0 := hy1 
      have hz2 : z > 0 := hz1 
      nlinarith [mul_pos hx2 hy2, mul_pos hy2 hz2, mul_pos hz2 hx2]
    have h5 : (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) - (3 * (x + y + z) / (2 * (x * y + y * z + z * x))) ≤ 0 := by 
      have pos1 : 0 < 2 * (x * y + y * z + z * x) := by
        nlinarith [h4]
      have pos2 : 0 < (x + y) * (y + z) * (z + x) := h3
      have h6 : (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) - (3 * (x + y + z) / (2 * (x * y + y * z + z * x))) =
          (2 * (x * y + y * z + z * x) * ((y + z) * (z + x) + (x + y) * (z + x) + (x + y) * (y + z)) - 3 * (x + y + z) * ((x + y) * (y + z) * (z + x))) / (2 * (x * y + y * z + z * x) * (x + y) * (y + z) * (z + x)) := by 
        field_simp 
        ring
      rw [h6]
      apply div_nonpos_of_nonpos_of_nonneg 
      · 
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
                  sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
                  mul_pos hx1 hy1, mul_pos hy1 hz1, mul_pos hz1 hx1, 
                  mul_pos (show 0 < x * y by nlinarith) (show 0 < y * z by nlinarith), 
                  mul_pos (show 0 < y * z by nlinarith) (show 0 < z * x by nlinarith), 
                  mul_pos (show 0 < z * x by nlinarith) (show 0 < x * y by nlinarith)
                ]
      · 
        positivity 
    linarith