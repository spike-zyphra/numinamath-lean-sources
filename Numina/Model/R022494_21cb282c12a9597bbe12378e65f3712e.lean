import Mathlib

def isOx (n : ℕ) := ∃ p q, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p < 100 ∧ q < 100 ∧ p * q = n

theorem number_theory_123519 :
    Set.ncard {x | x ∈ Finset.Icc 1 2021 ∧ isOx x} = 201 := by 
  have h1 : {x | x ∈ Finset.Icc 1 2021 ∧ isOx x} = Finset.filter (fun x => 
    x ≠ 0 ∧ (∃ p ∈ Finset.range 100, ∃ q ∈ Finset.range 100, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p * q = x)
    ) (Finset.Icc 1 2021) := by
    ext x
    simp [isOx]
    <;> try { 
      tauto 
    }
    <;> try { 
      intro hx
      rcases hx with ⟨hx1, hx2⟩
      have h2 : x ≥ 1 := by 
        omega
      have h3 : x ≠ 0 := by 
        omega
      simp [h2, h3]
      <;> tauto 
    }
    <;> try { 
      aesop 
    }
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide