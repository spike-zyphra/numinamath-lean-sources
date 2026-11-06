import Mathlib

theorem number_theory_180982 :
    Set.ncard {p : ℤ × ℤ | p.1 ^ 2 % 57 < p.2 ^ 2 % 57 ∧ 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 57} = 738 := by 
  have h1 : {p : ℤ × ℤ | p.1 ^ 2 % 57 < p.2 ^ 2 % 57 ∧ 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 57} = Finset.filter (fun p => (p.1 ^ 2 % 57 < p.2 ^ 2 % 57 ∧ 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 57)) (Finset.Icc (1 : ℤ) 57 ×ˢ Finset.Icc (1 : ℤ) 57) := by
    ext ⟨p, q⟩
    simp 
    omega 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide