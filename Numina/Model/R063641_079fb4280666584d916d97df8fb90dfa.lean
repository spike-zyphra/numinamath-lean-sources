import Mathlib

theorem number_theory_246778 :
    Set.ncard {p : ℕ × ℕ | p.1 + p.2 = 1000 ∧ ¬(∃ i, (Nat.digits 10 p.1).get i = 0) ∧ ¬(∃ i, (Nat.digits 10 p.2).get i = 0)} = 738 := by
  have h1 : {p : ℕ × ℕ | p.1 + p.2 = 1000 ∧ ¬(∃ i, (Nat.digits 10 p.1).get i = 0) ∧ ¬(∃ i, (Nat.digits 10 p.2).get i = 0)} = Finset.filter (fun p => p.1 + p.2 = 1000 ∧ ¬(∃ i, (Nat.digits 10 p.1).get i = 0) ∧ ¬(∃ i, (Nat.digits 10 p.2).get i = 0)) (Finset.Icc (0 : ℕ) 1000 ×ˢ Finset.Icc (0 : ℕ) 1000) := by
    ext ⟨a, b⟩
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide