import Mathlib

theorem algebra_178697 {f : ℝ → ℝ} (hf : ∀ x, f x = x^6 - 2 * Real.sqrt 2006 * x^5 - x^4 + x^3 - 2 * Real.sqrt 2007 * x^2 + 2 * x - Real.sqrt 2006) :
    f (Real.sqrt 2006 + Real.sqrt 2007) = Real.sqrt 2007 := by
  rw [hf]
  have h1 : Real.sqrt 2006 ^ 2 = 2006 := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt 2007 ^ 2 = 2007 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 2006 ^ 3 = 2006 * Real.sqrt 2006 := by
    calc
      Real.sqrt 2006 ^ 3 = Real.sqrt 2006 ^ 2 * Real.sqrt 2006 := by ring
      _ = 2006 * Real.sqrt 2006 := by rw [h1]
  have h4 : Real.sqrt 2007 ^ 3 = 2007 * Real.sqrt 2007 := by
    calc
      Real.sqrt 2007 ^ 3 = Real.sqrt 2007 ^ 2 * Real.sqrt 2007 := by ring
      _ = 2007 * Real.sqrt 2007 := by rw [h2]
  have h5 : Real.sqrt 2006 ^ 4 = 2006 ^ 2 := by
    calc
      Real.sqrt 2006 ^ 4 = (Real.sqrt 2006 ^ 2) ^ 2 := by ring
      _ = 2006 ^ 2 := by rw [h1]
  have h6 : Real.sqrt 2007 ^ 4 = 2007 ^ 2 := by
    calc
      Real.sqrt 2007 ^ 4 = (Real.sqrt 2007 ^ 2) ^ 2 := by ring
      _ = 2007 ^ 2 := by rw [h2]
  have h7 : Real.sqrt 2006 ^ 5 = (2006 ^ 2) * Real.sqrt 2006 := by
    calc
      Real.sqrt 2006 ^ 5 = Real.sqrt 2006 ^ 4 * Real.sqrt 2006 := by ring
      _ = (2006 ^ 2) * Real.sqrt 2006 := by rw [h5]
  have h8 : Real.sqrt 2007 ^ 5 = (2007 ^ 2) * Real.sqrt 2007 := by
    calc
      Real.sqrt 2007 ^ 5 = Real.sqrt 2007 ^ 4 * Real.sqrt 2007 := by ring
      _ = (2007 ^ 2) * Real.sqrt 2007 := by rw [h6]
  have h9 : Real.sqrt 2006 ^ 6 = 2006 ^ 3 := by
    calc
      Real.sqrt 2006 ^ 6 = (Real.sqrt 2006 ^ 2) ^ 3 := by ring
      _ = 2006 ^ 3 := by rw [h1]
  have h10 : Real.sqrt 2007 ^ 6 = 2007 ^ 3 := by
    calc
      Real.sqrt 2007 ^ 6 = (Real.sqrt 2007 ^ 2) ^ 3 := by ring
      _ = 2007 ^ 3 := by rw [h2]
  nlinarith [Real.sqrt_nonneg 2006, Real.sqrt_nonneg 2007, 
    h1, h2, 
    sq_nonneg (Real.sqrt 2006 - Real.sqrt 2007), 
    sq_nonneg (Real.sqrt 2006 + Real.sqrt 2007 - 1),
    mul_nonneg (Real.sqrt_nonneg 2006) (Real.sqrt_nonneg 2007),
    sq_nonneg (Real.sqrt 2006 + Real.sqrt 2007),
    sq_nonneg (Real.sqrt 2006 ^ 2 - 2006),
    sq_nonneg (Real.sqrt 2007 ^ 2 - 2007)
]