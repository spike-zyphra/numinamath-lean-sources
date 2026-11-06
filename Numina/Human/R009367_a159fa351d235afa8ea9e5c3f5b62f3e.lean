import Mathlib

theorem algebra_273749 {x y : ℕ} {px py : ℝ}(hx: x  = 4)(hp: px = 2 * py)(h_nonzero: py > 0 )(h' : x * py + y * px = 3/2 * (x * px + y * py)) :
     ((x / y) : ℚ)  = 1 / 4 := by 
    rw [hx, hp] at h'
    
    have h_simp : 8 + y * 4 = 24 + y * 3 := by 
      
      field_simp at h' 
      ring_nf at h' 
      have h1 : py * ( 8 + y * 4) = py * (24 + y * 3 ) := by 
        ring_nf 
        exact h'
      field_simp at h1 
      norm_cast at h1 
      cases h1 
      · assumption
      · exfalso
        aesop  
        
    have hy: y = 16 := by
      linarith [h_simp]

    rw [hx, hy] 
    ring 
