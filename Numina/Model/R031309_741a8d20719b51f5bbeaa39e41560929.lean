import Mathlib

theorem inequalities_301494 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Real.sqrt (x / (y + z)) + Real.sqrt (y / (z + x)) + Real.sqrt (z / (x + y)) ≥ 2 := by
  have h1 : Real.sqrt (x / (y + z)) ≥ 2 * x / (x + y + z) := by 
    have h11 : 0 < y + z := by linarith 
    have h12 : x / (y + z) ≥ 0 := by positivity 
    have h13 : (2 * x / (x + y + z)) ^2 ≤ x / (y + z) := by
      have h14 : 0 < x + y + z := by linarith 
      have h15 : 0 < (y + z) := by linarith 
      have h16 : (2 * x / (x + y + z)) ^ 2 = 4 * x ^ 2 / (x + y + z) ^ 2 := by 
        have h17 : 0 < x + y + z := by linarith 
        field_simp 
        <;> ring_nf 
      have h17 : x / (y + z) = x / (y + z) := by rfl 
      have h21 : (x * (x + y + z)^2) - (4 * x^2 * (y + z)) = x * (x - (y + z)) ^ 2 := by
        ring_nf 
      have h22 : 0 ≤ x * (x - (y + z)) ^ 2 := by
        positivity 
      have h30 : (2 * x / (x + y + z)) ^ 2 - x / (y + z) ≤ 0 := by 
        have h31 : (2 * x / (x + y + z)) ^2 - x / (y + z) = ( (4 * x^2 : ℝ) * (y + z) - x * (x + y + z)^2 ) / ( (y + z) * (x + y + z) ^ 2 ) := by
          field_simp
          <;> ring_nf 
        rw [h31] 
        apply div_nonpos_of_nonpos_of_nonneg 
        · -- Show that the numerator is ≤ 0 
          nlinarith [h21, sq_nonneg (x - (y + z)), mul_pos hx (show 0 < y + z by linarith)]
        · -- Show that the denominator is ≥ 0 
          positivity 
      linarith 
    have h14 : Real.sqrt (x / (y + z)) ≥ Real.sqrt ((2 * x / (x + y + z)) ^ 2) := by 
      apply Real.sqrt_le_sqrt 
      linarith [h13]
    have h15 : Real.sqrt ((2 * x / (x + y + z)) ^ 2) = (2 * x / (x + y + z)) := by 
      rw [Real.sqrt_sq] 
      positivity 
    linarith [h14, h15]

  have h2 : Real.sqrt (y / (z + x)) ≥ 2 * y / (x + y + z) := by 
    have h21 : 0 < z + x := by linarith 
    have h22 : y / (z + x) ≥ 0 := by positivity 
    have h23 : (2 * y / (x + y + z)) ^2 ≤ y / (z + x) := by 
      have h24 : 0 < x + y + z := by linarith 
      have h25 : 0 < (z + x) := by linarith 
      have h26 : (2 * y / (x + y + z)) ^ 2 = 4 * y ^ 2 / (x + y + z) ^ 2 := by 
        have h17 : 0 < x + y + z := by linarith 
        field_simp 
        <;> ring_nf 
      have h27 : y / (z + x) = y / (z + x) := by rfl 
      have h28 : (y * (x + y + z) ^ 2) - (4 * y ^2 * (z + x)) = y * (x - (y - z)) ^ 2 := by 
        ring_nf 
      have h29 : 0 ≤ y * (x - (y - z)) ^ 2 := by 
        positivity 
      have h30 : (2 * y / (x + y + z)) ^ 2 - y / (z + x) ≤ 0 := by 
        have h31 : (2 * y / (x + y + z)) ^2 - y / (z + x) = ( (4 * y ^ 2 : ℝ) * (z + x) - y * (x + y + z) ^ 2 ) / ( (z + x) * (x + y + z) ^ 2 ) := by 
          field_simp 
          <;> ring_nf 
        rw [h31] 
        apply div_nonpos_of_nonpos_of_nonneg 
        · -- Show that the numerator is ≤ 0 
          nlinarith [h28, sq_nonneg (x - (y - z)), mul_pos hy (show 0 < z + x by linarith)] 
        · -- Show that the denominator is ≥ 0 
          positivity 
      linarith 
    have h24 : Real.sqrt (y / (z + x)) ≥ Real.sqrt ((2 * y / (x + y + z)) ^ 2) := by 
      apply Real.sqrt_le_sqrt 
      linarith [h23]
    have h25 : Real.sqrt ((2 * y / (x + y + z)) ^ 2) = (2 * y / (x + y + z)) := by 
      rw [Real.sqrt_sq] 
      positivity 
    linarith [h24, h25]

  have h3 : Real.sqrt (z / (x + y)) ≥ 2 * z / (x + y + z) := by
    have h31 : 0 < x + y := by linarith
    have h32 : z / (x + y) ≥ 0 := by positivity
    have h33 : (2 * z / (x + y + z)) ^2 ≤ z / (x + y) := by
      have h34 : 0 < x + y + z := by linarith
      have h35 : 0 < (x + y) := by linarith
      have h36 : (2 * z / (x + y + z)) ^ 2 = 4 * z ^ 2 / (x + y + z) ^ 2 := by
        have h17 : 0 < x + y + z := by linarith 
        field_simp 
        <;> ring_nf 
      have h37 : z / (x + y) = z / (x + y) := by rfl 
      have h38 : (z * (x + y + z) ^ 2) - (4 * z ^2 * (x + y)) = z * (x + y - z) ^ 2 := by
        ring_nf 
      have h39 : 0 ≤ z * (x + y - z) ^ 2 := by 
        positivity 
      have h40 : (2 * z / (x + y + z)) ^ 2 - z / (x + y) ≤ 0 := by 
        have h41 : (2 * z / (x + y + z)) ^2 - z / (x + y) = ( (4 * z^2 : ℝ) * (x + y) - z * (x + y + z)^2 ) / ( (x + y) * (x + y + z) ^ 2 ) := by 
          field_simp 
          <;> ring_nf 
        rw [h41] 
        apply div_nonpos_of_nonpos_of_nonneg 
        · -- Show that the numerator is ≤ 0 
          nlinarith [h38, sq_nonneg (x + y - z), mul_pos hz (show 0 < x + y by linarith)] 
        · -- Show that the denominator is ≥ 0 
          positivity 
      linarith 
    have h34 : Real.sqrt (z / (x + y)) ≥ Real.sqrt ((2 * z / (x + y + z)) ^ 2) := by 
      apply Real.sqrt_le_sqrt 
      linarith [h33]
    have h35 : Real.sqrt ((2 * z / (x + y + z)) ^ 2) = (2 * z / (x + y + z)) := by 
      rw [Real.sqrt_sq] 
      positivity 
    linarith [h34, h35]

  have h4 : Real.sqrt (x / (y + z)) + Real.sqrt (y / (z + x)) + Real.sqrt (z / (x + y)) ≥ 2 * x / (x + y + z) + 2 * y / (x + y + z) + 2 * z / (x + y + z) := by 
    linarith [h1, h2, h3]
  have h5 : 2 * x / (x + y + z) + 2 * y / (x + y + z) + 2 * z / (x + y + z) = 2 := by 
    field_simp 
    <;> ring 
  linarith [h4, h5]