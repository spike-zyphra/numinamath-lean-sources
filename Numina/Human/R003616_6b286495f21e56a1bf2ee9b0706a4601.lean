import Mathlib

/-
X. Khanov

Prove that the numbers from 1 to 15 cannot be divided into two groups: $A$ consisting of two numbers and $B$ consisting of 13 numbers, such that the sum of the numbers in group $B$ is equal to the product of the numbers in group $A$.
-/

theorem number_theory_201925 : ¬ (∃ A B : Finset ℕ, A ∩ B = ∅ ∧ A ∪ B = Finset.Icc 1 15 ∧ A.card = 2 ∧ B.card = 13 ∧ ∑ i ∈ B, i = ∏ i ∈ A, i) := by 
  by_contra h
  obtain ⟨A,B,hcap,huni, ha, hb, h⟩ := h

  rw [Finset.card_eq_two] at ha
  obtain ⟨x,y,xney, ha ⟩ := ha
  
  have cla1 : ∑ i ∈ A, i + ∑ i ∈ B, i = ∑ i ∈ (A ∪ B), i := by 
    refine Eq.symm (Finset.sum_union ?_)
    exact Finset.disjoint_iff_inter_eq_empty.mpr hcap
  rw [huni] at cla1
  have :  ∑ i ∈ Finset.Icc 1 15, i = 120 := by decide
  rw [this] at cla1
  rw [h] at cla1

  have eq : x+y + x*y = 120 := by
    have t1: ∑ i ∈ A, i = x+y := by simp [ha]; exact Finset.sum_pair xney
    have t2: ∏ i ∈ A, i = x*y := by simp [ha]; exact Finset.prod_pair xney
    rw [t1,t2] at cla1
    exact cla1
  
  have eq2 : (x+1) * (y+1) = 121 := by linarith
  have di121 : Nat.divisors 121 = {1,11,121} := by decide
  have xp1d : (x+1) ∣ 121 := by use (y+1); linarith
  have : (x+1) ∈ Nat.divisors 121 := by 
    refine Nat.mem_divisors.mpr ?_
    simp [xp1d]
  rw [di121] at this
  simp at this

  have xin115: x ∈ Finset.Icc 1 15 := by 
    have xinA : x ∈ A:= by simp [ha]
    have Asub115 : A ⊆ Finset.Icc 1 15 := by 
      rw [← huni]
      simp
    exact (Asub115 xinA)
    
  rcases this with (xe | xe | xe)



  -- case x=0
  simp [xe] at xin115

  -- case x=10
  simp [xe] at eq
  have ye : y = 10 := by omega
  have xey : x = y := by linarith
  contradiction

  -- case x=120
  simp [xe] at xin115
