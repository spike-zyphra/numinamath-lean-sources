import Mathlib

open Real

theorem inequalities_315703 (α β : ℝ) (h : ∀ x y z, α * (x * y + y * z + z * x) ≤
    sqrt (x ^ 2 + x * y + y ^ 2) * sqrt (y ^ 2 + y * z + z ^ 2) +
      sqrt (y ^ 2 + y * z + z ^ 2) * sqrt (z ^ 2 + z * x + x ^ 2) +
      sqrt (z ^ 2 + z * x + x ^ 2) * sqrt (x ^ 2 + x * y + y ^ 2) ∧
    sqrt (x ^ 2 + x * y + y ^ 2) * sqrt (y ^ 2 + y * z + z ^ 2) +
      sqrt (y ^ 2 + y * z + z ^ 2) * sqrt (z ^ 2 + z * x + x ^ 2) +
      sqrt (z ^ 2 + z * x + x ^ 2) * sqrt (x ^ 2 + x * y + y ^ 2) ≤
    β * (x ^ 2 + y ^ 2 + z ^ 2)) :
    α ≤ 3 ∧ β ≥ 3 := by

  have h1 := h 1 1 1

  have h2 : sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) = sqrt 3 := by
    norm_num
  
  have h5 : sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) * sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) = 3 := by
    rw [h2]
    have h6 : sqrt 3 * sqrt 3 = (3 : ℝ) := by
      calc
        sqrt 3 * sqrt 3 = (sqrt 3) ^ 2 := by ring
        _ = (3 : ℝ) := by rw [Real.sq_sqrt]; norm_num
    linarith
  
  -- First inequality: $\alpha * 3 \leq 9$ hence $\alpha \leq 3$
  have h_alpha : α ≤ 3 := by
    have h8 : α * (1 * 1 + 1 * 1 + 1 * 1) = 3 * α := by
      ring_nf
    have h9 : sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) * sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) + 
        sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) * sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) + 
        sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) * sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) = 9 := by
      linarith [h5]
    
    have h10 : α * (1 * 1 + 1 * 1 + 1 * 1) ≤ 
        sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) * sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) + 
        sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) * sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) + 
        sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) * sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) := by 
      linarith [h1.1]

    nlinarith [h8, h9, h10]

  have h_beta : β ≥ 3 := by
    have h12 : sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) * sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) + 
        sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) * sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) + 
        sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) * sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) = 9 := by 
      linarith [h5]
    
    have h11 : sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) * sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) + 
      sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) * sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) + 
      sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) * sqrt (1 ^ 2 + 1 * 1 + 1 ^ 2) ≤ 
      β * (1 ^ 2 + 1 ^ 2 + 1 ^ 2) := by 
      linarith [h1.2]

    nlinarith [h12, h11]

  exact ⟨h_alpha, h_beta⟩