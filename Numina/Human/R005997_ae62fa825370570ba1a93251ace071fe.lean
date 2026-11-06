import Mathlib

/-
Theorem: Calculate the total number of phone numbers John needs to try
-/
theorem Combinatorics_611018
    (A₁ : a₁ = a.choose b * 2)
    (A : a = 4)
    (B : b = 2)
    (A₂ : a₂ = c.choose d)
    (C : c = 2)
    (D : d = 1)
    (A₃ : a₃ = e.choose f)
    (E : e = 10)
    (F : f = 1)
    (A₄ : a₄ = a₁ * a₂ * a₃) :
    a₄ = 240 := by 

  -- Calculate the value of the first combinatorial term as 12
  have hA₁ : a₁ = 12 := by 
    rw [A,B] at A₁
    aesop

  -- Calculate the value of the second combinatorial term as 2
  have hA₂ : a₂ = 2 := by
    rw [C,D] at A₂
    aesop

  -- Calculate the value of the third combinatorial term as 10
  have hA₃ : a₃ = 10 := by 
    rw [E,F] at A₃
    aesop
    
  rw [hA₁ , hA₂ , hA₃] at A₄
  omega