import Mathlib

theorem algebra_285843 {a : ℕ → ℝ} (ha : ∃ r, ∀ n, a n = a 0 * r ^ n)
    (ha2 : a 2 = Real.sqrt 2) (ha3 : a 3 = 3 ^ ((1 : ℝ) / 3)) :
    (a 0 + a 2010) / (a 6 + a 2016) = 8 / 9 := by
  rcases ha with ⟨r, hr⟩
  have ha2' : a 2 = a 0 * r ^ 2 := hr 2
  rw [ha2'] at ha2
  have ha3' : a 3 = a 0 * r ^ 3 := hr 3
  rw [ha3'] at ha3
  have eq1 : r ≠ 0 := by
    by_contra h
    rw [h] at ha2
    norm_num at ha2
    all_goals nlinarith [Real.sqrt_nonneg 2, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
  have eq2 : a 0 + a 2010 = a 0 * (1 + r ^ 2010) := by
    have h1 : a 2010 = a 0 * r ^ 2010 := hr 2010
    linarith
  have eq3 : a 6 + a 2016 = a 0 * r ^ 6 * (1 + r ^ 2010) := by
    have h1 : a 6 = a 0 * r ^ 6 := hr 6
    have h2 : a 2016 = a 0 * r ^ 2016 := hr 2016
    calc
      a 6 + a 2016 = a 0 * r ^ 6 + a 0 * r ^ 2016 := by rw [h1, h2]
      _ = a 0 * r ^ 6 + a 0 * r ^ 6 * r ^ 2010 := by ring_nf
      _ = a 0 * r ^ 6 * (1 + r ^ 2010) := by ring
  have eq5 : a 0 ≠ 0 := by
    by_contra h
    rw [h] at ha2
    have h1 : Real.sqrt 2 = 0 := by
      nlinarith
    have h2 : Real.sqrt 2 > 0 := by
      apply Real.sqrt_pos.mpr
      all_goals linarith
    linarith
  have eq3' : (a 0 + a 2010) / (a 6 + a 2016) = 1 / r ^ 6 := by
    rw [eq2, eq3]
    have h14 : 1 + r ^ 2010 ≠ 0 := by
      have h10 : r ^ 2010 ≥ 0 := by positivity
      nlinarith
    have h13 : a 0 ≠ 0 := eq5
    have h11 : r ^ 6 ≠ 0 := by positivity
    field_simp [h13, h11, h14]
    all_goals nlinarith [show r ^ 2010 ≥ 0 by positivity, show r ^ 6 > 0 by positivity]
  have eq10 : a 0 * r ^ 2 = Real.sqrt 2 := by
    linarith
  have eq11 : a 0 * r ^ 3 = (3 : ℝ) ^ ((1 : ℝ) / 3) := by
    linarith
  have eq13 : r ^ 6 = 9 / 8 := by
    have h13_eq : r = ((3 : ℝ) ^ ((1 : ℝ) / 3)) / Real.sqrt 2 := by
      have h1 : a 0 * r ^ 2 = Real.sqrt 2 := eq10
      have h2 : a 0 * r ^ 3 = (3 : ℝ) ^ ((1 : ℝ) / 3) := eq11
      -- derive r by dividing second eq by first.
      -- a0 * r^3 / (a0 * r^2) = (3^(1/3)) / (sqrt 2)
      -- r = (3^(1/3)) / (sqrt 2)
      have h4 : r = (a 0 * r ^ 3) / (a 0 * r ^ 2) := by
        have ha0r2_ne : a 0 * r ^ 2 ≠ 0 := by
          apply mul_ne_zero
          exact eq5
          have : r ^ 2 ≠ 0 := by
            rw [pow_two]
            exact mul_ne_zero eq1 eq1
          assumption
        field_simp [ha0r2_ne]
        all_goals nlinarith
      have h5 : (a 0 * r ^ 3) / (a 0 * r ^ 2) = ((3 : ℝ) ^ ((1 : ℝ) / 3)) / Real.sqrt 2 := by
        have h10' : a 0 * r ^ 3 = (3 : ℝ) ^ ((1 : ℝ) / 3) := by linarith
        have h11' : a 0 * r ^ 2 = Real.sqrt 2 := by linarith
        rw [h10', h11']
      have h15 : r = ((3 : ℝ) ^ ((1 : ℝ) / 3)) / Real.sqrt 2 := by
        have h18 : r = (a 0 * r ^ 3) / (a 0 * r ^ 2) := h4
        rw [h18]
        rw [h5]
      exact h15
    rw [h13_eq]
    have eq19 : (((3 : ℝ) ^ ((1 : ℝ) / 3)) / Real.sqrt 2) ^ 6 = (9 / 8 : ℝ) := by
      have eq20 : (((3 : ℝ) ^ ((1 : ℝ) / 3)) / Real.sqrt 2) ^ 6 = ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 6 / (Real.sqrt 2) ^ 6 := by
        field_simp
      rw [eq20]
      have eq21 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 6 = (9 : ℝ) := by
        have eq20 : ((3 : ℝ) ^ ((1 : ℝ) / 3)) ^ 6 = (3 : ℝ) ^ (2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring_nf
          all_goals
            norm_num
        have eq21 : (3 : ℝ) ^ (2 : ℝ) = (9 : ℝ) := by
          norm_num
        rw [eq21] at eq20
        linarith
      have eq22 : (Real.sqrt 2 : ℝ) ^ 6 = (8 : ℝ) := by
        have h10 : (Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) := by
          rw [Real.sq_sqrt]
          all_goals
            norm_num
        have h13 : (Real.sqrt 2 : ℝ) ^ 6 = ((Real.sqrt 2 : ℝ) ^ 2) ^ 3 := by ring
        rw [h13, h10]
        norm_num
      rw [eq21, eq22]
      all_goals
        norm_num
    linarith
  rw [eq3', eq13]
  all_goals
    norm_num