import Mathlib

theorem number_theory_146945 :
    Set.ncard {p : ℕ × ℕ | p.1 ∈ Finset.Icc 100 999 ∧ p.2 ∈ Finset.Icc 100 999 ∧ Nat.digits 10 p.1 = List.reverse (Nat.digits 10 p.2) ∧ p.1 - p.2 = 297} = 60 := by
  have h1 : {p : ℕ × ℕ | p.1 ∈ Finset.Icc 100 999 ∧ p.2 ∈ Finset.Icc 100 999 ∧ Nat.digits 10 p.1 = List.reverse (Nat.digits 10 p.2) ∧ p.1 - p.2 = 297} = Finset.filter (fun p : ℕ × ℕ => Nat.digits 10 p.1 = List.reverse (Nat.digits 10 p.2) ∧ p.1 - p.2 = 297) (Finset.Icc (100 : ℕ) 999 ×ˢ Finset.Icc (100 : ℕ) 999) := by
    ext ⟨a, b⟩
    simp [Finset.mem_Icc]
    <;> try tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide