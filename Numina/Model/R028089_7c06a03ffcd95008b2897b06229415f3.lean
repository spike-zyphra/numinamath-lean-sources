import Mathlib

theorem inequalities_601060 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    |(1 / (1 + x ^ 3)) - (1 / (1 + y ^ 3))| < |x - y| := by 
  have h1 : (1 / (1 + x ^ 3) : ℝ) - (1 / (1 + y ^ 3) : ℝ) = (y^3 - x^3) / ((1 + x^ 3) * (1 + y ^ 3)) := by
    field_simp
    <;> ring
  have h2 : |(1 / (1 + x ^ 3) - (1 / (1 + y ^ 3)))| = |(y ^ 3 - x ^ 3) / ((1 + x^ 3) * (1 + y ^ 3))| := by
    rw [h1]
  have h3 : |(y ^ 3 - x ^ 3) / ((1 + x ^ 3) * (1 + y ^ 3))| = |y ^ 3 - x ^ 3| / |(1 + x ^ 3) * (1 + y ^ 3)| := by
    field_simp [abs_div]

  have h4 : |(1 + x ^ 3) * (1 + y ^ 3)| = |(1 + x^3)| * |(1 + y^3)| := by
    simp [abs_mul]

  have hx1 : 0 < (1 + x^ 3 : ℝ) := by
    positivity

  have hy1 : 0 < (1 + y^ 3 : ℝ) := by
    positivity

  have h5 : |(1 + x^3)| = (1 + x^ 3 : ℝ) := by
    rw [abs_of_pos hx1]
  
  have h6 : |(1 + y^3)| = (1 + y ^ 3 : ℝ) := by
    rw [abs_of_pos hy1]

  have h7 : |(1 + x^ 3) * (1 + y ^ 3)| = (1 + x^3) * (1 + y ^ 3) := by
    rw [h4, h5, h6]
  
  have h8 : |(1 / (1 + x ^ 3) - (1 / (1 + y ^ 3)))| = |y ^ 3 - x ^ 3| / ((1 + x ^ 3) * (1 + y ^ 3)) := by
    rw [h2, h3, h7]
    all_goals norm_num [h4, h5, h6]
  
  have h9 : |(y ^ 3 - x ^ 3)| = |y - x| * (x ^ 2 + x * y + y ^ 2) := by
    have h10 : (y ^ 3 - x^ 3 : ℝ) = (y - x) * (x ^ 2 + x * y + y ^ 2) := by
      ring_nf
    have h11 : |(y ^ 3 - x ^ 3)| = |y - x| * |x ^ 2 + x * y + y ^ 2| := by
      rw [h10]
      apply abs_mul

    have h12 : x ^ 2 + x * y + y ^ 2 > 0 := by
      positivity

    have h13 : |(x ^ 2 + x * y + y ^ 2)| = x ^ 2 + x * y + y ^ 2 := by
      exact abs_of_pos h12

    rw [h13] at h11
    linarith

  have h12' : |y ^ 3 - x ^ 3| / ((1 + x ^ 3) * (1 + y ^ 3)) = |x - y| * ((x ^ 2 + x * y + y^ 2) / ((1 + x ^ 3) * (1 + y ^ 3)))
    := by
    rw [h9]
    have h12' : |y - x| = |x - y| := by
      have habs : |y - (x : ℝ)| = |x - (y : ℝ)| := by
        apply abs_sub_comm
      have h : |x - (y : ℝ)| = |x - y| := by
        ring_nf at *
      linarith [habs, h]
    rw [h12']
    <;> ring_nf <;> norm_num


  have h14 : (x ^ 2 + x * y + y ^ 2) / ((1 + x ^ 3) * (1 + y ^ 3)) < 1 := by
    have h15 : (x ^ 2 + x * y + y ^ 2) < (1 + x^3) * (1 + y ^ 3) := by
      nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne hxy), sq_nonneg (x - y), sq_nonneg (x - y), sq_nonneg (x * y - 1), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 - y ^ 2),
          sq_nonneg (x ^ 3 - y ^ 3), sq_nonneg (x ^ 3 - y ^ 3),
          mul_pos hx hy,
          sq_nonneg (x - 1), sq_nonneg (y - 1),
          sq_nonneg (x + y), sq_nonneg (x * y), sq_nonneg (x - y), sq_nonneg (x * y - 1),
          sq_nonneg ((1 + x^2) - (1 + y^2)), sq_nonneg ((x)^3 - (y)^3)]
    have h16 : (1 + x^3) * (1 + y ^ 3) > 0 := by positivity
    apply (div_lt_one (by positivity)).mpr
    nlinarith
  
  have h13' : |x - (y : ℝ)| > 0 := by
    apply abs_pos.2
    intro h
    apply hxy
    linarith

  rw [h8, h12']
  nlinarith [abs_nonneg (x - y), abs_nonneg ((x ^ 3 - y ^ 3) / ((1 + x ^ 3) * (1 + y ^ 3))), h14, h13']