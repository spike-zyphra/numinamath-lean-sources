import Mathlib

/-
The volume of a rectangular prism is 21 . Its length, width and height are all different positive integers. The sum of its length, width and height is
(A) 11
(B) 13
(C) 15
(D) 9
(E) 17
-/

theorem number_theory (a b c : ℕ) (h: a*b*c = 21) (aneb : a ≠ b) (anec : a ≠ c) (bnec : b ≠ c) : a + b + c = 11 := by

  -- a b c have to be the divisors of 21 = {1, 3, 7, 21}.
  have di21 : Nat.divisors 21 = {1,3,7,21} := by decide

  have ad : a ∣ 21 := by use b*c; linarith
  have bd : b ∣ 21 := by use a*c; nlinarith
  have cd : c ∣ 21 := by use a*b; linarith
  have ain: a ∈ Nat.divisors 21 := by 
    refine Nat.mem_divisors.mpr ?_
    simp [ad]
  have bin: b ∈ Nat.divisors 21 := by 
    refine Nat.mem_divisors.mpr ?_
    simp [bd]
  have cin: c ∈ Nat.divisors 21 := by 
    refine Nat.mem_divisors.mpr ?_
    simp [cd]
  
  -- Only {1,3,7} can satisfy all the assumptions.
  simp [di21] at ain bin cin
  rcases ain with ae | ae | ae | ae <;>
  rcases bin with be | be | be | be <;>
  rcases cin with ce | ce | ce | ce <;>
  simp [ae,be,ce] at h aneb anec bnec<;>
  simp [ae,be,ce]
  
