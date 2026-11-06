import Mathlib

theorem mercury_liquid_balance 
    {v s S' h h' v' : ℝ}  
    (h₀ : v > 0)  
    (h₁ : s > 0)  
    (h₂ : S' > 0)  
    (h₃ : h > 0)   
    (h₄ : h' > 0)  
    (h₅ : v' > 0)  
    (h₆ : s < S')  
    (h_balance : v * s = v' * S')  
    (h_height_ratio : h / h' = v / v') :   
    h - h' = h / S' * (S' - s) 
    := by
  -- From h_height_ratio: $h / h' = v / v'$ cross multiply to get $h \cdot v' = v \cdot h'$.  
  have h_eq1 : h * v' = v * h' := by 
    have h1 : h / h' = v / v' := h_height_ratio
    field_simp [(show h' ≠ 0 by linarith), (show v' ≠ 0 by linarith)] at h1 ⊢
    all_goals linarith
  -- From $h \cdot v' = v \cdot h'$, we can write $h' = \frac{h \cdot v'}{v}$.  
  have h_eq2 : h' = (h * v') / v := by 
    field_simp [(show v ≠ 0 by linarith)]
    all_goals linarith [h_eq1]
  -- $v' = \frac{v \cdot s}{S'}$, from the balance equations.  
  have h_eq3 : v' = (v * s) / S' := by 
    have h3 : v * s = v' * S' := h_balance
    field_simp [(show S' ≠ 0 by linarith)]
    all_goals linarith
  -- Now, compute $h'$.  
  have h_eq4 : h' = h * s / S' := by
    have h_eq5 : h' = (h * v') / v := h_eq2
    rw [h_eq5]
    have h_eq6 : v' = (v * s) / S' := h_eq3
    rw [h_eq6]
    field_simp [(show v ≠ 0 by linarith), (show S' ≠ 0 by linarith)]
    <;> ring
  -- Now, compute $h - h'$.  
  have h_eq7 : h - h' = h / S' * (S' - s) := by
    rw [h_eq4]
    field_simp [(show S' ≠ 0 by linarith)]
    <;> ring_nf 
  exact h_eq7