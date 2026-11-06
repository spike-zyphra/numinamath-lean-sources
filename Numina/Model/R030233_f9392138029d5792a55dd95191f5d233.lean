import Mathlib

theorem algebra_200338 (z1 z2 z3 : ℂ) (hz1 : ‖z1‖ = 1) (hz2 : ‖z2‖ = 1) (hz3 : ‖z3‖ = 1)
    (hr : ‖z1 + z2 + z3‖ = r) :
    (z1 / z2 + z2 / z3 + z3 / z1).re = (r ^ 2 - 3) / 2 := by
  have h1 : z1 ≠ 0 := by
    by_contra h
    have h0 : ‖z1‖ = 0 := by
      rw [h]
      simp
    rw [h0] at hz1
    all_goals
      linarith
  have h2 : z2 ≠ 0 := by
    by_contra h
    have h0 : ‖z2‖ = 0 := by
      rw [h]
      simp
    rw [h0] at hz2
    all_goals
      linarith
  have h3 : z3 ≠ 0 := by
    by_contra h
    have h0 : ‖z3‖ = 0 := by
      rw [h]
      simp
    rw [h0] at hz3
    all_goals
      linarith
  have h1' : z1.re ^ 2 + z1.im ^ 2 = 1 := by
    have h11 : ‖z1‖ = Real.sqrt (z1.re ^ 2 + z1.im ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> ring_nf
    rw [h11] at hz1
    have h00 : Real.sqrt (z1.re ^ 2 + z1.im ^ 2) = 1 := hz1
    have h01 : z1.re ^ 2 + z1.im ^ 2 ≥ 0 := by positivity
    have h02 : z1.re ^ 2 + z1.im ^ 2 = (1 : ℝ) := by
      calc
        z1.re ^ 2 + z1.im ^ 2 = (Real.sqrt (z1.re ^ 2 + z1.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = 1 ^ 2 := by
          rw [h00]
        _ = (1 : ℝ) := by norm_num
    linarith
  have h2' : z2.re ^ 2 + z2.im ^ 2 = 1 := by
    have h22 : ‖z2‖ = Real.sqrt (z2.re ^ 2 + z2.im ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      all_goals ring_nf
    rw [h22] at hz2
    have h00 : Real.sqrt (z2.re ^ 2 + z2.im ^ 2) = 1 := hz2
    have h01 : z2.re ^ 2 + z2.im ^ 2 ≥ 0 := by positivity
    have h02 : z2.re ^ 2 + z2.im ^ 2 = (1 : ℝ) := by
      calc
        z2.re ^ 2 + z2.im ^ 2 = (Real.sqrt (z2.re ^ 2 + z2.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = 1 ^ 2 := by
          rw [h00]
        _ = (1 : ℝ) := by norm_num
    linarith
  have h3' : z3.re ^ 2 + z3.im ^ 2 = 1 := by
    have h33 : ‖z3‖ = Real.sqrt (z3.re ^ 2 + z3.im ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      all_goals ring_nf
    rw [h33] at hz3
    have h00 : Real.sqrt (z3.re ^ 2 + z3.im ^ 2) = 1 := hz3
    have h01 : z3.re ^ 2 + z3.im ^ 2 ≥ 0 := by positivity
    have h02 : z3.re ^ 2 + z3.im ^ 2 = (1 : ℝ) := by
      calc
        z3.re ^ 2 + z3.im ^ 2 = (Real.sqrt (z3.re ^ 2 + z3.im ^ 2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = 1 ^ 2 := by
          rw [h00]
        _ = (1 : ℝ) := by norm_num
    linarith
  have h4 : r = Real.sqrt ((z1.re + z2.re + z3.re) ^ 2 + (z1.im + z2.im + z3.im) ^ 2) := by
    have h11 : ‖z1 + z2 + z3‖ = Real.sqrt ((z1.re + z2.re + z3.re) ^ 2 + (z1.im + z2.im + z3.im) ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq, add_mul, mul_add, pow_two]
      all_goals ring_nf
    rw [h11] at hr
    linarith
  have h5 : r ^ 2 = (z1.re + z2.re + z3.re) ^ 2 + (z1.im + z2.im + z3.im) ^ 2 := by
    calc
      r ^ 2 = (Real.sqrt ((z1.re + z2.re + z3.re) ^ 2 + (z1.im + z2.im + z3.im) ^ 2)) ^ 2 := by
        rw [show r = Real.sqrt ((z1.re + z2.re + z3.re) ^ 2 + (z1.im + z2.im + z3.im) ^ 2) by exact h4]
      _ = (z1.re + z2.re + z3.re) ^ 2 + (z1.im + z2.im + z3.im) ^ 2 := by
        rw [Real.sq_sqrt]
        positivity
  have h6 : (z1 / z2 + z2 / z3 + z3 / z1).re = (r ^ 2 - 3) / 2 := by
    have h7 : (z1 / z2 + z2 / z3 + z3 / z1).re = (z1.re * z2.re + z1.im * z2.im) / (z2.re ^ 2 + z2.im ^ 2) + (z2.re * z3.re + z2.im * z3.im) / (z3.re ^ 2 + z3.im ^ 2) + (z3.re * z1.re + z3.im * z1.im) / (z1.re ^ 2 + z1.im ^ 2) := by
      simp [Complex.div_re, Complex.normSq, Complex.div_im]
      all_goals ring_nf
    rw [h7]
    have h8 : (z1.re * z2.re + z1.im * z2.im) / (z2.re ^ 2 + z2.im ^ 2) = z1.re * z2.re + z1.im * z2.im := by
      rw [h2']
      all_goals linarith
    have h9 : (z2.re * z3.re + z2.im * z3.im) / (z3.re ^ 2 + z3.im ^ 2) = z2.re * z3.re + z2.im * z3.im := by
      rw [h3']
      all_goals linarith
    have h10 : (z3.re * z1.re + z3.im * z1.im) / (z1.re ^ 2 + z1.im ^ 2) = z3.re * z1.re + z3.im * z1.im := by
      rw [h1']
      all_goals linarith
    rw [h8, h9, h10]
    nlinarith
  exact h6