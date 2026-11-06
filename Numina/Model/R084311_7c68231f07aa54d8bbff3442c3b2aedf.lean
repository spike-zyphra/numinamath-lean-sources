import Mathlib

theorem number_theory_206323 :
    {(n, m) : ℕ × ℕ | n ∈ Finset.Icc 10 99 ∧ m ∈ Finset.Icc 10 99 ∧ Nat.digits 10 (n + m) = List.reverse (Nat.digits 10 (n - m))}.ncard = 9 := by
  have h1 : {(n, m) : ℕ × ℕ | n ∈ Finset.Icc 10 99 ∧ m ∈ Finset.Icc 10 99 ∧ Nat.digits 10 (n + m) = List.reverse (Nat.digits 10 (n - m))} = Finset.filter (fun p => Nat.digits 10 (p.1 + p.2) = List.reverse (Nat.digits 10 (p.1 - p.2))) (Finset.Icc (10 : ℕ) 99 ×ˢ Finset.Icc (10 : ℕ) 99) := by
    ext ⟨n, m⟩
    simp [Finset.mem_Icc]
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide