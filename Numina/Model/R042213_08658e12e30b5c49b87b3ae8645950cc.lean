import Mathlib

open Real

theorem algebra_184449 {x a : ℝ} (ha : 0 < a) (hx : a < x) :
    ((sqrt (x - a)) / (sqrt (x + a) + sqrt (x - a)) +
     (x - a) / (sqrt (x^2 - a^2) - x + a)) / sqrt ((x^2 / a^2) - 1) = 1 := by
  have h1 : 0 < x - a := by linarith
  have h2 : 0 < x + a := by nlinarith
  have h3 : sqrt (x ^ 2 - a ^ 2) = sqrt (x - a) * sqrt (x + a) := by
    have h4 : x ^ 2 - a ^ 2 = (x - a) * (x + a) := by
      nlinarith
    have h5 : sqrt (x ^ 2 - a ^ 2) = sqrt ((x - a) * (x + a)) := by 
      rw [h4]
    have h6 : sqrt ((x - a) * (x + a)) = sqrt (x - a) * sqrt (x + a) := by
      rw [Real.sqrt_mul]
      all_goals
        nlinarith
    rw [h5, h6]
  have h7 : sqrt ((x ^ 2 / a ^ 2) - 1) = sqrt (x^2 - a^2) / a := by
    have h8 : (x ^ 2 / a ^ 2 : ℝ) - 1 = (x^2 - a^2) / (a ^ 2 : ℝ) := by
      field_simp
      <;> nlinarith
    rw [h8]
    have h9 : 0 < a ^ 2 := by
      nlinarith [ha]
    have h10 : sqrt ((x^2 - a^2) / (a ^ 2 : ℝ)) = sqrt (x^2 - a^2) / sqrt (a ^ 2) := by 
      rw [Real.sqrt_div]
      all_goals
        nlinarith
    rw [h10]
    have h11 : sqrt (a ^ 2 : ℝ) = a := by
      rw [Real.sqrt_sq]
      linarith
    rw [h11]
  have h8 : sqrt (x - a) / (sqrt (x + a) + sqrt (x - a)) = (sqrt (x^2 - a^2) - (x - a)) / (2 * a) := by
    have h3' : sqrt (x + a) + sqrt (x - a) > 0 := by
      have h10 : 0 < sqrt (x + a) := by
        apply Real.sqrt_pos.mpr
        linarith
      have h11 : 0 < sqrt (x - a) := by
        apply Real.sqrt_pos.mpr
        linarith
      linarith [h10, h11]
    field_simp [h3]
    <;> nlinarith [Real.sqrt_nonneg (x - a), Real.sqrt_nonneg (x + a),
      Real.sq_sqrt (show 0 ≤ x - a by linarith), Real.sq_sqrt (show 0 ≤ x + a by linarith),
      Real.sqrt_nonneg (x^2 - a^2), mul_nonneg (Real.sqrt_nonneg (x-a)) (Real.sqrt_nonneg (x+a)), Real.sq_sqrt (show 0 ≤ x^2 - a^2 by nlinarith)]
  have h9 : (x - a) / (sqrt (x^2 - a^2) - x + a) = (sqrt (x^2 - a^2) + (x - a)) / (2 * a) := by
    have h10 : (sqrt (x^2 - a^2) - x + a) ≠ 0 := by
      by_contra h_eq
      have h11 : sqrt (x^2 - a^2) = x - a := by
        nlinarith [h_eq, Real.sqrt_nonneg (x^2 - a^2)]
      have h12 : x^2 - a^2 = (x - a) ^ 2 := by
        calc
          x^2 - a^2 = (sqrt (x^2 - a^2)) ^ 2 := by rw [Real.sq_sqrt]; nlinarith
          _ = (x - a) ^ 2 := by rw [h11]
      have h13 : x^2 - a^2 = x^2 - 2 * a * x + a^2 := by
        nlinarith [h12]
      have h14 : 2 * a * x = 2 * a^2 := by
        nlinarith [h13]
      have h15 : x = a := by
        nlinarith [h14, ha.ne']
      linarith [h15, hx]
    field_simp [h10]
    <;> nlinarith [Real.sqrt_nonneg (x^2 - a^2), Real.sq_sqrt (show 0 ≤ x^2 - a^2 by nlinarith), 
      sq_pos_of_pos ha, sq_pos_of_pos (show 0 < x - a by linarith), 
      mul_nonneg (Real.sqrt_nonneg (x-a)) (Real.sqrt_nonneg (x+a)), Real.sq_sqrt (show 0 ≤ x - a by linarith), 
      Real.sq_sqrt (show 0 ≤ x + a by linarith)]
  have eq1 : (sqrt (x - a)) / (sqrt (x + a) + sqrt (x - a)) + (x - a) / (sqrt (x^2 - a^2) - x + a) = sqrt (x^2 - a^2) / a := by
    rw [h8, h9]
    field_simp [show 0 < a by linarith, Real.sqrt_pos.mpr (show 0 < x^2 - a^2 by nlinarith)]
    <;> nlinarith [Real.sqrt_nonneg (x^2 - a^2), mul_nonneg (Real.sqrt_nonneg (x-a)) (Real.sqrt_nonneg (x+a)), Real.sq_sqrt (show 0 ≤ x^2 - a^2 by nlinarith)]
  rw [eq1, h7]
  have hx1_pos : sqrt (x ^ 2 - a ^ 2) > 0 := by
    apply Real.sqrt_pos.mpr
    nlinarith
  have hx1_ne_zero : sqrt (x ^ 2 - a ^ 2) ≠ 0 := by
    linarith [hx1_pos]
  have eq4 : (sqrt (x ^ 2 - a^2) / a) / (sqrt (x ^ 2 - a^2) / a) = 1 := by
    field_simp [show a ≠ 0 by linarith, hx1_ne_zero]
    all_goals
      try ring_nf <;> norm_num
      <;> try nlinarith
      all_goals
        try { 
          exfalso
          <;> nlinarith 
        }
  exact eq4