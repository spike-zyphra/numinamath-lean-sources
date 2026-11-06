import Mathlib

theorem algebra_292262 :
    IsLeast {x : ℝ | ∃ s t : ℝ, x = (s + 5 - 3 * abs (Real.cos t))^2 + (s - 2 * abs (Real.sin t))^2} 2 := by
  constructor
  · -- Show 2 is in the set
    use -1, 0
    have h1 : Real.cos (0 : ℝ) = 1 := Real.cos_zero
    have h2 : Real.sin (0 : ℝ) = 0 := Real.sin_zero
    norm_num [abs_of_nonneg, h1, h2]
  · -- Show 2 is the minimum in the set
    intro x hx 
    rcases hx with ⟨s, t, h_eq⟩
    have h1 : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
    have h2 : abs (Real.sin t) ≥ 0 := by apply abs_nonneg 
    have h3 : abs (Real.cos t) ≥ 0 := by apply abs_nonneg 
    have h4 : (abs (Real.sin t)) ^ 2 + (abs (Real.cos t)) ^ 2 = 1 := by 
      have h11 : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t 
      have h12 : (abs (Real.sin t)) ^ 2 = Real.sin t ^ 2 := by 
        rw [sq_abs]
      have h13 : (abs (Real.cos t)) ^ 2 = Real.cos t ^ 2 := by 
        rw [sq_abs]
      linarith [h11, h12, h13]
    have h7 : (s + 5 - 3 * abs (Real.cos t)) ^ 2 + (s - 2 * abs (Real.sin t)) ^ 2 ≥ 2 := by 
      have h8 : abs (Real.cos t) ≤ 1 := by 
        apply abs_le.mpr 
        constructor <;> 
          (try norm_num) <;> 
            (try linarith [Real.neg_one_le_cos t, Real.cos_le_one t])
      have h9 : abs (Real.sin t) ≤ 1 := by 
        apply abs_le.mpr 
        constructor <;> 
          (try norm_num) <;> 
            (try linarith [Real.neg_one_le_sin t, Real.sin_le_one t])
      nlinarith [sq_nonneg (s + 1), sq_nonneg (abs (Real.cos t) - 1), sq_nonneg (abs (Real.sin t) - 0), 
        sq_nonneg ( (s + 1) ), 
        sq_nonneg ( abs (Real.cos t) -1 ), 
        sq_nonneg ( abs (Real.sin t) -0 ), 
        sq_nonneg ( (s + 1) - abs (Real.sin t) ), 
        mul_nonneg (show (0 : ℝ) ≤ abs (Real.sin t) by positivity) 
          (show (0 : ℝ) ≤ abs (Real.cos t) by positivity), 
        Real.sin_sq_add_cos_sq t, 
        sq_nonneg ( (abs (Real.sin t)) ^ 2 - (abs (Real.cos t)) ^ 2 )
      ]
    have h8 : x = (s + 5 - 3 * abs (Real.cos t)) ^ 2 + (s - 2 * abs (Real.sin t)) ^ 2 := by 
      linarith [h_eq]
    linarith [h8, h7]