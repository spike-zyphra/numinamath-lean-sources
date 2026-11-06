import Mathlib
open Real Set
open scoped Real

theorem algebra_24700 (x : ℝ) : (1 - sin x ^ 5 - cos x ^ 5) = (1 - sin x) * (1 - cos x) * (3 + 2 * (sin x + cos x) + 2 * sin x * cos x + sin x * cos x * (sin x + cos x)):= by
  have h1 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x

  have eq1 : (1 - sin x ^ 5 - cos x ^ 5) = (1 - sin x) * (1 - cos x) * (3 + 2 * (sin x + cos x) + 2 * sin x * cos x + sin x * cos x * (sin x + cos x)) := by 
    have h10 : sin x ^ 2 + cos x ^ 2 = 1 := h1
  
    -- derive sin x^3
    have h2 : sin x ^ 3 = sin x * (1 - cos x ^ 2) := by
      have h21 : sin x ^ 2 = 1 - cos x ^ 2 := by
        linarith [h10]
      calc 
        sin x ^ 3 = sin x * sin x ^ 2 := by ring
        _ = sin x * (1 - cos x ^ 2) := by rw [h21]
  
    -- derive cos x^3
    have h3 : cos x ^ 3 = cos x * (1 - sin x ^ 2) := by 
      have h31 : cos x ^ 2 = 1 - sin x ^ 2 := by 
        linarith [h10]
      calc 
        cos x ^ 3 = cos x * cos x ^ 2 := by ring
        _ = cos x * (1 - sin x ^ 2) := by rw [h31]

    -- derive sin x^4
    have h4 : sin x ^ 4 = (1 - cos x ^ 2) ^ 2 := by
      have h41 : sin x ^ 2 = 1 - cos x ^ 2 := by 
        linarith [h10]
      calc 
        sin x ^ 4 = (sin x ^ 2) ^ 2 := by ring
        _ = (1 - cos x ^ 2) ^ 2 := by rw [h41]

    -- derive cos x^4
    have h5 : cos x ^ 4 = (1 - sin x ^ 2) ^ 2 := by 
      have h51 : cos x ^ 2 = 1 - sin x ^ 2 := by 
        linarith [h10]
      calc 
        cos x ^ 4 = (cos x ^ 2) ^ 2 := by ring
        _ = (1 - sin x ^ 2) ^ 2 := by rw [h51]

    -- derive sin x^5
    have h6 : sin x ^ 5 = sin x * (1 - cos x ^ 2) ^ 2 := by 
      calc 
        sin x ^ 5 = sin x ^ 2 * sin x ^ 3 := by ring
        _ = (1 - cos x ^ 2) * sin x ^ 3 := by
          have h41 : sin x ^ 2 = 1 - cos x ^ 2 := by
            linarith [h10]
          rw [h41]
        _ = (1 - cos x ^ 2) * (sin x * (1 - cos x ^ 2)) := by 
          rw [h2]
        _ = sin x * (1 - cos x ^ 2) ^ 2 := by ring
  
    -- derive cos x^5
    have h7 : cos x ^ 5 = cos x * (1 - sin x ^ 2) ^ 2 := by 
      calc 
        cos x ^ 5 = cos x ^ 2 * cos x ^ 3 := by ring 
        _ = (1 - sin x ^ 2) * cos x ^ 3 := by 
          have h51 : cos x ^ 2 = 1 - sin x ^ 2 := by
            linarith [h10]
          rw [h51]
        _ = (1 - sin x ^ 2) * (cos x * (1 - sin x ^ 2)) := by 
          rw [h3]
        _ = cos x * (1 - sin x ^ 2) ^ 2 := by ring
  
    calc 
       1 - sin x ^ 5 - cos x ^ 5 = 1 - (sin x * (1 - cos x ^ 2) ^ 2) - (cos x * (1 - sin x ^ 2) ^ 2) := by 
        rw [h6, h7]
  
      _ = (1 - sin x) * (1 - cos x) * (3 + 2 * (sin x + cos x) + 2 * sin x * cos x + sin x * cos x * (sin x + cos x)) := by 
        nlinarith [sq_nonneg (sin x ^ 2 + cos x ^ 2 - 1), sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x), sq_nonneg (sin x), sq_nonneg (cos x), sq_nonneg (sin x * cos x), sq_nonneg (sin x ^ 2 - cos x ^ 2), Real.sin_sq_add_cos_sq x, sq_nonneg (sin x ^ 2), sq_nonneg (cos x ^ 2)]
  
  exact eq1