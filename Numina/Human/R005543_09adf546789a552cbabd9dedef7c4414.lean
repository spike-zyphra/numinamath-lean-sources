import Mathlib
open Real

/-
Use combinatorial mathematics and probability theory to prove:
Among 5 coin tosses, given that "exactly 2 heads appear in the first three tosses" and "exactly 2 heads appear in the last three tosses",
the probability that "the third toss is a head" is 4/5.
-/
theorem Combinatorics_608743
    (An : n = 2) 
    (Ak : k = 1)    
    (Ahk : hk = 2)       
    (APH : PH = 1/2)     
    (APT : PT = 1 - PH)  
    (AC : (C : ℝ) = n.choose k)
    (AhC : (hC : ℝ) = n.choose hk) 
    (AP : P = C * PH ^ k * PT ^ (n - k))
    (AP₁: P₁ = P * PH * P)
    (AP₂ : P₂ = P₃ + P₄)
    (AP₃ : P₃ = P₁)     
    (AP₄ : P₄ = hC * PH ^ hk * PH * hC * PH ^ hk):  
    P₁ / P₂ = (4 / 5 : ℝ) := by
    
  norm_num [An, Ak, Ahk, APH, APT] at *

  rw [AC] at AP
  ring_nf at AP

  rw [AP] at AP₁ 
  ring_nf at AP₁

  rw [AhC] at AP₄
  ring_nf at AP₄
   
  rw [AP₁] at AP₃

  rw [AP₃,AP₄] at AP₂

  field_simp
  linarith
   

  
  