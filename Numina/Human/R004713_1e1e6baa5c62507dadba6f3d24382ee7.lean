import Mathlib

/-The article in the fifth issue of our journal in 1983,titled "A Simple Method for Compiling Radical Equations," states that the equation √(5x-1) +√2x=3x-1 "will produce a quartic equation after squaring twice, which may be quite troublesome to solve." In fact, this equation can be solved using a simpler method.-/
theorem algebra_308204 (x : ℝ) (hx : 0 ≤ 5 * x - 1) (h : Real.sqrt (5 * x - 1) + Real.sqrt (2 * x) = 3 * x - 1) :
    x = 2 := by
  have h1 : 0 ≤ Real.sqrt (5 * x - 1) := Real.sqrt_nonneg (5 * x - 1)
  have h2 : 0 ≤ Real.sqrt (2 * x) := Real.sqrt_nonneg (2 * x)
  have h3 : 0 ≤ 3 * x - 1 := by linarith [h, h1, h2]
  have eq1 : Real.sqrt (5 * x - 1) + Real.sqrt (2 * x) = 3 * x - 1 := h
  have h4 : Real.sqrt (5 * x - 1) ≥ 0 := Real.sqrt_nonneg (5 * x - 1)
  have h5 : Real.sqrt (2 * x) ≥ 0 := Real.sqrt_nonneg (2 * x)
  have eq2 : Real.sqrt (5 * x - 1) = 3 * x - 1 - Real.sqrt (2 * x) := by linarith
  have h6 : (Real.sqrt (5 * x - 1)) ^ 2 = (3 * x - 1 - Real.sqrt (2 * x)) ^ 2 := by
    rw [eq2]
  have h7 : 5 * x - 1 = (3 * x - 1 - Real.sqrt (2 * x)) ^ 2 := by
    have h8 : (Real.sqrt (5 * x - 1)) ^ 2 = 5 * x - 1 := by
      rw [Real.sq_sqrt]
      linarith
    linarith [h6, h8]
  have h9 : (3 * x - 1 - Real.sqrt (2 * x)) ^ 2 = (3 * x - 1) ^ 2 - 2 * (3 * x - 1) * Real.sqrt (2 * x) + (Real.sqrt (2 * x)) ^ 2 := by ring
  rw [h9] at h7
  have h10 : (Real.sqrt (2 * x)) ^ 2 = 2 * x := by
    apply Real.sq_sqrt
    linarith [show 0 ≤ 2 * x by nlinarith [h2]]
  rw [h10] at h7
  have h11 : (3 * x - 1) ^ 2 = 9 * x^2 - 6 * x + 1 := by ring
  rw [h11] at h7
  have eq3 : 9 * x^2 - 9 * x + 2 = 2 * (3 * x - 1) * Real.sqrt (2 * x) := by nlinarith [h7, h2]
  have h12 : 0 ≤ 9 * x^2 - 9 * x + 2 := by nlinarith [sq_nonneg (3 * x - 1), sq_nonneg (Real.sqrt (2 * x)), eq3]
  have eq4 : (9 * x^2 - 9 * x + 2) ^ 2 = (2 * (3 * x - 1) * Real.sqrt (2 * x)) ^ 2 := by
    rw [eq3]
  have h13 : (9 * x^2 - 9 * x + 2) ^ 2 = (2 * (3 * x - 1) * Real.sqrt (2 * x)) ^ 2 := by linarith [eq4]
  have h14 : (2 * (3 * x - 1) * Real.sqrt (2 * x)) ^ 2 = 4 * (3 * x - 1) ^ 2 * (Real.sqrt (2 * x)) ^ 2 := by
    ring_nf
  have h15 : (Real.sqrt (2 * x)) ^ 2 = 2 * x := by
    refine Real.sq_sqrt (by linarith [show (0 : ℝ) ≤ 2 * x by nlinarith [h2]])
  rw [h14, h15] at h13
  ring_nf at h13
  have h16 : 81 * x^4 - 234 * x^3 + 165 * x^2 - 44 * x + 4 = 0 := by
    nlinarith [h13]
  have h17 : (x - 2) * (x - 1 / 3) * (3 * x - 1) * (9 * x - 2) = 0 := by
    ring_nf at h16 ⊢
    linarith
  -- From h17 we decude that there are only four cases for x --
  cases' (mul_eq_zero.mp h17) with h18 h19
  · cases' (mul_eq_zero.mp h18) with h20 h21
    · cases' (mul_eq_zero.mp h20) with h22 h23
      · -- x - 2 = 0 
        linarith
      · -- x - 1/3 = 0 
        have h24 : x = 1 / 3 := by linarith
        have h25 : Real.sqrt (5 * x - 1) + Real.sqrt (2 * x) = 3 * x - 1 := h
        rw [h24] at h25
        have h26 : Real.sqrt (5 * (1 / 3 : ℝ) - 1) + Real.sqrt (2 * (1 / 3 : ℝ)) = 3 * (1 / 3 : ℝ) - 1 := by
          linarith
        have h27 : Real.sqrt (5 * (1 / 3 : ℝ) - 1) = Real.sqrt (2 / 3 : ℝ) := by norm_num [Real.sqrt_eq_iff_eq_sq]
        have h28 : Real.sqrt (2 * (1 / 3 : ℝ)) = Real.sqrt (2 / 3 : ℝ) := by norm_num [Real.sqrt_eq_iff_eq_sq]
        rw [h27, h28] at h26
        have h29 : Real.sqrt (2 / 3 : ℝ) > 0 := by
          apply Real.sqrt_pos.mpr
          norm_num
        linarith [h29]
    · -- 3x - 1 = 0 
      have h24 : x = 1 / 3 := by linarith
      have h25 : Real.sqrt (5 * x - 1) + Real.sqrt (2 * x) = 3 * x - 1 := h
      rw [h24] at h25
      have h26 : Real.sqrt (5 * (1 / 3 : ℝ) - 1) + Real.sqrt (2 * (1 / 3 : ℝ)) = 3 * (1 / 3 : ℝ) - 1 := by
        linarith
      have h27 : Real.sqrt (5 * (1 / 3 : ℝ) - 1) = Real.sqrt (2 / 3 : ℝ) := by norm_num [Real.sqrt_eq_iff_eq_sq]
      have h28 : Real.sqrt (2 * (1 / 3 : ℝ)) = Real.sqrt (2 / 3 : ℝ) := by norm_num [Real.sqrt_eq_iff_eq_sq]
      rw [h27, h28] at h26
      have h29 : Real.sqrt (2 / 3 : ℝ) > 0 := by
        apply Real.sqrt_pos.mpr
        norm_num
      linarith [h29]
  · -- 9x - 2 = 0 
    have h24 : x = 2 / 9 := by linarith
    have h25 : Real.sqrt (5 * x - 1) + Real.sqrt (2 * x) = 3 * x - 1 := h
    rw [h24] at h25
    have h26 : Real.sqrt (5 * (2 / 9 : ℝ) - 1) + Real.sqrt (2 * (2 / 9 : ℝ)) = 3 * (2 / 9 : ℝ) - 1 := by
      linarith
    have h27 : Real.sqrt (5 * (2 / 9 : ℝ) - 1) = 1 / 3 := by
      rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
    have h28 : Real.sqrt (2 * (2 / 9 : ℝ)) = 2 / 3 := by
      rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
    rw [h27, h28] at h26
    norm_num at h26
    