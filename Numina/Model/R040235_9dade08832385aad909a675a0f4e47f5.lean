import Mathlib

open Real

theorem inequalities_158407 (x : ℝ) :
    (x + (1/2)*sin (2*x))*(x - (1/2)*sin (2*x)) ≥ sin x ^ 4 := by
  have h1 : sin (2 * x) = 2 * sin x * cos x := by 
    rw [sin_two_mul]

  have h2 : (x + (1 / 2) * sin (2 * x)) * (x - (1 / 2) * sin (2 * x)) =
      x^2 - (1 / 4) * sin (2 * x) ^ 2 := by 
    ring
  
  have h3 : (x + (1 / 2) * sin (2 * x)) * (x - (1 / 2) * sin (2 * x)) =
      x^2 - sin x ^ 2 * cos x ^ 2 := by 
    rw [h2]
    rw [h1]
    <;> ring_nf <;> simp [sin_sq, cos_sq] 
    <;> ring
  
  have h4 : x ^ 2 - sin x ^ 2 * cos x ^ 2 ≥ sin x ^ 4 := by
    have h5 : x ^ 2 ≥ sin x ^ 2 := by
      have h6 : sin x ^ 2 ≤ x ^ 2 := by
        have h7 : |sin x| ≤ |x| := by
          apply abs_sin_le_abs
        have h8 : (sin x) ^ 2 ≤ x ^ 2 := by
          have h9 : |sin x| ≤ |x| := h7
          have h10 : (|sin x|) ^ 2 ≤ (|x|) ^ 2 := by
            nlinarith [abs_nonneg (sin x), abs_nonneg x, h9]
          have h11 : (|sin x|) ^ 2 = (sin x) ^ 2 := by
            simp [sq_abs]
          have h12 : (|x|) ^ 2 = x ^ 2 := by
            simp [sq_abs]
          nlinarith [h11, h12, h10]
        linarith
      linarith
      all_goals linarith
      all_goals nlinarith
  
    have h11 : sin x ^ 2 * cos x ^ 2 = sin x ^ 2 * (1 - sin x ^ 2) := by
      have h12 : cos x ^ 2 = 1 - sin x ^ 2 := by
        have h13 : cos x ^ 2 + sin x ^ 2 = 1 := by
          exact Real.cos_sq_add_sin_sq x
        linarith
      rw [h12]
      <;> ring
  
    nlinarith [h5, sq_nonneg (x^2 - 1), sq_nonneg (sin x ^ 2 - 1), Real.sin_sq_le_one x, Real.sin_sq_add_cos_sq x, sq_nonneg (x - sin x), sq_nonneg (x + sin x)]
  
  linarith [h3, h4]
  all_goals linarith
  all_goals nlinarith