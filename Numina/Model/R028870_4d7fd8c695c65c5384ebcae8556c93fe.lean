import Mathlib

theorem algebra_21248 :
    
    (Set.ncard {(x, y): ℤ × ℤ | x ∈ Finset.Icc 1 5 ∧ y ∈ Finset.Icc 1 5 ∧ x + y > x * y}) / 25 = 9 / 25 := by
have h1 : Set.ncard {(x, y): ℤ × ℤ | x ∈ Finset.Icc 1 5 ∧ y ∈ Finset.Icc 1 5 ∧ x + y > x * y} = 9 := by
    have h3 : {(x, y): ℤ × ℤ | x ∈ Finset.Icc 1 5 ∧ y ∈ Finset.Icc 1 5 ∧ x + y > x * y} = Finset.filter (fun p : ℤ × ℤ => 
      (p.1 ≥ 1 ∧ p.1 ≤ 5) ∧ (p.2 ≥ 1 ∧ p.2 ≤ 5) ∧ (p.1 + p.2 > p.1 * p.2)
    ) (Finset.Icc (-10 : ℤ) 10 ×ˢ Finset.Icc (-10 : ℤ) 10) := by
      ext ⟨x, y⟩
      simp [Finset.mem_Icc]
      omega
    rw [h3]
    rw [Set.ncard_coe_Finset]
    native_decide
  
calc
  (Set.ncard {(x, y): ℤ × ℤ | x ∈ Finset.Icc 1 5 ∧ y ∈ Finset.Icc 1 5 ∧ x + y > x * y}) / 25 
    = 9 / 25 := by rw [h1]