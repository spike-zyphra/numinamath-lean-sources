import Mathlib

open Real

theorem inequalities_323340 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (f : ℝ) (hf : f = max (max (x / (x + y) + y / (y + z) + z / (z + x)) (y / (x + y) + z / (y + z) + x / (z + x))) (z / (x + y) + x / (y + z) + y / (z + x))) :
    f ≥ 3 / 2 := by
  have h1 : 0 < x + y := by nlinarith
  have h2 : 0 < y + z := by nlinarith
  have h3 : 0 < z + x := by nlinarith

  have h4 : f ≥ 3 / 2 := by
    rw [hf]
    by_contra h
    push_neg at h

    have h5 : max (max (x / (x + y) + y / (y + z) + z / (z + x)) (y / (x + y) + z / (y + z) + x / (z + x))) (z / (x + y) + x / (y + z) + y / (z + x)) < 3 / 2 := by
      linarith [h]

    have h6 : x / (x + y) + y / (y + z) + z / (z + x) < 3 / 2 := by
      have h11 : max (max (x / (x + y) + y / (y + z) + z / (z + x)) (y / (x + y) + z / (y + z) + x / (z + x))) (z / (x + y) + x / (y + z) + y / (z + x)) ≥ x / (x + y) + y / (y + z) + z / (z + x) := by
        simp [max_le_iff]
      linarith [h11, h5]

    have h7 : y / (x + y) + z / (y + z) + x / (z + x) < 3 / 2 := by
      have h12 : max (max (x / (x + y) + y / (y + z) + z / (z + x)) (y / (x + y) + z / (y + z) + x / (z + x))) (z / (x + y) + x / (y + z) + y / (z + x)) ≥ y / (x + y) + z / (y + z) + x / (z + x) := by
        simp [max_le_iff]
      linarith [h12, h5]

    have h8 : z / (x + y) + x / (y + z) + y / (z + x) < 3 / 2 := by
      have h13 : max (max (x / (x + y) + y / (y + z) + z / (z + x)) (y / (x + y) + z / (y + z) + x / (z + x))) (z / (x + y) + x / (y + z) + y / (z + x)) ≥ z / (x + y) + x / (y + z) + y / (z + x) := by
        simp [max_le_iff]
      linarith [h13, h5]

    have h9 : x / (x + y) + y / (y + z) + z / (z + x) + (y / (x + y) + z / (y + z) + x / (z + x)) + (z / (x + y) + x / (y + z) + y / (z + x)) ≥ 9 / 2 := by
      have hx1 : 0 < x := by linarith
      have hy1 : 0 < y := by linarith
      have hz1 : 0 < z := by linarith
      have h1 : 0 < x + y := by nlinarith
      have h2 : 0 < y + z := by nlinarith
      have h3 : 0 < z + x := by nlinarith
      have h4 : x / (x + y) + y / (y + z) + z / (z + x) + (y / (x + y) + z / (y + z) + x / (z + x)) + (z / (x + y) + x / (y + z) + y / (z + x)) = (x + y + z) * (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) := by
        field_simp
        ring
      rw [h4]
      have h5 : (x + y + z) * (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥ 9 / 2 := by
        have h6 : 0 < (x + y) * (y + z) * (z + x) := by positivity
        have h7 : (x + y + z) * (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) - 9 / 2 ≥ 0 := by
          have h8 : (x + y + z) * (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) - 9 / 2 = ((x + y + z) * ( (y + z) * (z + x) + (x + y) * (z + x) + (x + y) * (y + z) ) - (9 / 2) * ( (x + y) * (y + z) * (z + x) ) ) / ( (x + y) * (y + z) * (z + x) ) := by
            field_simp
            ring
          rw [h8]
          apply div_nonneg
          nlinarith [sq_nonneg (x + y + z), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, sq_nonneg (x * y + y * z + z * x - (x * y * (x + y + z) / 3)), sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y)]
          all_goals positivity
        linarith
      linarith

    have h11 : (x / (x + y) + y / (y + z) + z / (z + x)) + (y / (x + y) + z / (y + z) + x / (z + x)) + (z / (x + y) + x / (y + z) + y / (z + x)) < 9 / 2 := by
      nlinarith [h6, h7, h8]

    linarith [h9, h11]

  linarith [h4]