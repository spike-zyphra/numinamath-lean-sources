import Mathlib

theorem algebra_144884 {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 2 - 3 * x + 2) :
    Set.ncard {x | f (f x) = 0} = 4 := by
  have h1 : {x | f (f x) = 0} = { (3 + Real.sqrt 5) / 2, (3 - Real.sqrt 5) / 2, (0 : ℝ), (3 : ℝ) } := by
    ext x 
    simp [hf]
    constructor
    · -- Assume f(f(x)) = 0, prove x ∈ { (3 + Real.sqrt 5) / 2, (3 - Real.sqrt 5) / 2, (0 : ℝ), (3 : ℝ) }
      intro h 
      have h2 : (x ^ 2 - 3 * x + 2) ^ 2 - 3 * (x ^ 2 - 3 * x + 2) + 2 = 0 := by nlinarith
      have h3 : (x ^ 2 - 3 * x + 2 - 1) * (x ^ 2 - 3 * x + 2 - 2) = 0 := by nlinarith 
      cases' (mul_eq_zero.1 h3) with h4 h5 
      · -- Case where the first factor is zero: x^2 - 3 x + 1 = 0
        have h6 : x ^ 2 - 3 * x + 1 = 0 := by nlinarith 
        have h7 : (x - (3 + Real.sqrt 5) / 2) * (x - (3 - Real.sqrt 5) / 2) = 0 := by
          nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        cases' (mul_eq_zero.1 h7) with h8 h9 
        · -- Case where x - (3 + √5)/2 = 0
          left
          linarith
        · -- Case where x - (3 - √5)/2 = 0
          right
          left
          linarith
      · -- Case where the second factor is zero: x^2 - 3 x = 0
        have h8 : x ^ 2 - 3 * x = 0 := by nlinarith 
        have h9 : x * (x - 3) = 0 := by nlinarith
        cases' (mul_eq_zero.1 h9) with h10 h11 
        · -- Case where x = 0
          right
          right
          left
          linarith
        · -- Case where x - 3 = 0
          right
          right
          right
          linarith
    · -- Assume x ∈ { (3 + Real.sqrt 5) / 2, (3 - Real.sqrt 5) / 2, (0 : ℝ), (3 : ℝ) }, prove f(f(x)) = 0
      rintro (h | h | h | h)
      · -- Case x = (3 + Real.sqrt 5) / 2
        rw [h]
        nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      · -- Case x = (3 - Real.sqrt 5) / 2
        rw [h]
        nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      · -- Case x = 0
        rw [h]
        norm_num
      · -- Case x = 3
        rw [h]
        norm_num
  rw [h1]
  have h2 : Real.sqrt 5 > 0 := by
    apply Real.sqrt_pos.mpr
    all_goals norm_num
  have h3 : (3 + Real.sqrt 5 : ℝ) / 2 ≠ (3 - Real.sqrt 5 : ℝ) / 2 := by
    intro h
    have h1 : 3 + Real.sqrt 5 = 3 - Real.sqrt 5 := by
      linarith [h]
    have h2 : Real.sqrt 5 = 0 := by
      nlinarith 
    linarith [show 0 < Real.sqrt 5 by nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ] ]
  have h4 : (3 + Real.sqrt 5 : ℝ) / 2 ≠ (0 : ℝ) := by 
    intro h 
    have h_eq : (3 + Real.sqrt 5 : ℝ) = 0 := by
      linarith 
    have h_eq2 : (Real.sqrt 5 : ℝ) = -3 := by
      nlinarith 
    have h10 : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have h11 : (-3 : ℝ) ^ 2 = 9 := by norm_num 
    nlinarith [h_eq2]
  have h5 : (3 + Real.sqrt 5 : ℝ) / 2 ≠ (3 : ℝ) := by 
    intro h 
    have h_eq : (3 + Real.sqrt 5 : ℝ) = 6 := by
      linarith 
    have h_eq2 : (Real.sqrt 5 : ℝ) = 3 := by
      nlinarith 
    have h10 : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have h11 : (3 : ℝ) ^ 2 = 9 := by norm_num 
    nlinarith [h_eq2]
  have h6 : (3 - Real.sqrt 5 : ℝ) / 2 ≠ (0 : ℝ) := by
    intro h 
    have h_eq : (3 - Real.sqrt 5 : ℝ) = 0 := by
      linarith 
    have h_eq2 : (Real.sqrt 5 : ℝ) = 3 := by
      nlinarith 
    have h10 : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have h11 : (3 : ℝ) ^ 2 = 9 := by norm_num 
    nlinarith [h_eq2]
  have h7 : (3 - Real.sqrt 5 : ℝ) / 2 ≠ (3 : ℝ) := by 
    intro h 
    have h_eq : (3 - Real.sqrt 5 : ℝ) = 6 := by
      linarith 
    have h_eq2 : (Real.sqrt 5 : ℝ) = -3 := by
      nlinarith 
    have h10 : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have h11 : (-3 : ℝ) ^ 2 = 9 := by norm_num 
    nlinarith [h_eq2]
  have h8 : (0 : ℝ) ≠ (3 : ℝ) := by 
    by_contra h 
    nlinarith 
  have h9 : ((3 + Real.sqrt 5 : ℝ) / 2 : ℝ) ≠ ((3 - Real.sqrt 5) / 2 : ℝ) := h3
  have h10 : ((3 + Real.sqrt 5 : ℝ) / 2 : ℝ) ≠ ((0 : ℝ)) := h4
  have h11 : ((3 + Real.sqrt 5 : ℝ) / 2 : ℝ) ≠ ((3 : ℝ)) := h5
  have h12 : ((3 - Real.sqrt 5 : ℝ) / 2 : ℝ) ≠ ((0 : ℝ)) := h6
  have h13 : ((3 - Real.sqrt 5 : ℝ) / 2 : ℝ) ≠ ((3 : ℝ)) := h7
  have h14 : ((0 : ℝ)) ≠ ((3 : ℝ)) := h8
  norm_num [Set.ncard_insert_of_not_mem, h9, h10, h11, h12, h13, h14]