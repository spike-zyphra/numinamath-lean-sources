import Mathlib

/-
23. Given 5 numbers: $a_{1}=1, a_{2}=-1, a_{3}=-1, a_{4}=1, a_{5}=-1$. The following numbers are determined as follows: $a_{6}=a_{1} \cdot a_{2}, a_{7}=a_{2} \cdot a_{3}, a_{8}=a_{3} \cdot a_{4}$ and so on. What is $a_{1988}$?
-/

theorem algebra_235115 (a : ℕ→ℤ) (ha1: ((a 1) = (1:ℤ))) (ha2: a 2 = -1) (ha3: a 3 = -1) (ha4 : a 4 = 1) (ha5: a 5 = -1) (h: ∀n≥6, a n = a (n-5)* a (n-4)): a 1988 = -1 := by 

  --We prove that the value of a goes like 1 -1 -1 1 -1 -1...
  have lem : ∀k:ℕ, a (6*k+1)=1 ∧a (6*k+2)=-1 ∧ a (6*k+3)=-1 ∧ a (6*k+4)=1 ∧ a (6*k+5)=-1 ∧ a (6*k+6)=-1  := by

    intro k
    induction' k with k hk

    simp [ha1,ha2,ha3,ha4,ha5]
    specialize h 6 (by norm_num)
    simp [ha1,ha2] at h
    exact h

    obtain ⟨h1,h2,h3,h4,h5,h6⟩ := hk
    have h7 : a (6 * (k + 1) + 1) = 1  := by 
      specialize h (6*(k+1)+1) (by linarith)
      rw [h]
      have e1: 6 * (k + 1) + 1 - 5 = 6*k+2 := by omega
      have e2: (6 * (k + 1) + 1 - 4)  =  6*k+3 := by omega
      rw [e1,e2]
      simp [h2,h3]
    have h8 : a (6 * (k + 1) + 2) = -1  := by 
      specialize h (6*(k+1)+2) (by linarith)
      rw [h]
      have e1: 6 * (k + 1) + 2 - 5 = 6*k+3 := by omega
      have e2: (6 * (k + 1) + 2 - 4)  =  6*k+4 := by omega
      rw [e1,e2]
      simp [h3,h4]
    have h9 : a (6 * (k + 1) + 3) = -1  := by 
      specialize h (6*(k+1)+3) (by linarith)
      rw [h]
      have e1: 6 * (k + 1) + 3 - 5 = 6*k+4 := by omega
      have e2: (6 * (k + 1) + 3 - 4)  =  6*k+5 := by omega
      rw [e1,e2]
      simp [h4,h5]
    have h10 : a (6 * (k + 1) + 4) = 1  := by 
      specialize h (6*(k+1)+4) (by linarith)
      rw [h]
      have e1: 6 * (k + 1) + 4 - 5 = 6*k+5 := by omega
      have e2: (6 * (k + 1) + 4 - 4)  =  6*k+6 := by omega
      rw [e1,e2]
      simp [h5,h6]
    have h11 : a (6 * (k + 1) + 5) = -1  := by 
      specialize h (6*(k+1)+5) (by linarith)
      rw [h]
      have e1: 6 * (k + 1) + 5 - 5 = 6*k+6 := by omega
      have e2: (6 * (k + 1) + 5 - 4)  =  6*(k+1)+1 := by omega
      rw [e1,e2]
      simp [h6,h7]
    have h12 : a (6 * (k + 1) + 6) = -1  := by 
      specialize h (6*(k+1)+6) (by linarith)
      rw [h]
      have e1: 6 * (k + 1) + 6 - 5 = 6*(k+1) +1 := by omega
      have e2: (6 * (k + 1) + 6 - 4)  =  6*(k+1)+2 := by omega
      rw [e1,e2]
      simp [h7,h8]
    tauto

  --Since 1988 = 6 * 331 + 2, we have a 1988 = -1.
  specialize lem 331
  norm_num at lem
  tauto