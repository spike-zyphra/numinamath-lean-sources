import Mathlib

open Matrix

theorem calculus_15953 {k : ℝ}
    (h : ∀ a b c : Fin 3 → ℝ, a + b + c = 0 →
      k • (b ×₃ a) + b ×₃ c + c ×₃ a = 0) :
    k = 2 := by

  have eq1 := h (fun i => 
          if i = 0 then (1 : ℝ) else 
            if i = 1 then (0 : ℝ) else 
              (0 : ℝ)) 
        (fun i => 
          if i = 0 then (0 : ℝ) else 
            if i = 1 then (1 : ℝ) else 
              (0 : ℝ)) 
        (fun i => 
          if i = 0 then (-1 : ℝ) else 
            if i = 1 then (-1 : ℝ) else 
              (0 : ℝ)) 
        (by 
          funext i 
          fin_cases i <;> simp )
  have eq2 : k = 2 := by 
    simp [crossProduct, Fin.sum_univ_three] at eq1 
    norm_num at eq1
    linarith 
  exact eq2