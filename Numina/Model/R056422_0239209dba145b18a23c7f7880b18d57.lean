import Mathlib

/- From the nine positive integers $1～9$, if any three are chosen, then the probability that these three numbers are pairwise coprime is ___          ___. -/
theorem number_theory_8482 :
    (Finset.Icc 1 9).card = 9 ∧
    {x : Finset ℕ | x ⊆ (Finset.Icc 1 9) ∧ x.card = 3 ∧ ∀ m ∈ x, ∀ n ∈ x, m ≠ n → Nat.Coprime m n}.ncard = 37 := by
  constructor
  · -- Simple calculation: the set {1, 2, 3, 4, 5, 6, 7, 8, 9} has 9 elements.
    simp
  · have : {x : Finset ℕ | x ⊆ (Finset.Icc 1 9) ∧ x.card = 3 ∧ ∀ m ∈ x, ∀ n ∈ x, m ≠ n → Nat.Coprime m n} = Finset.filter (fun s => ∀ m ∈ s, ∀ n ∈ s, m ≠ n → Nat.Coprime m n) (Finset.powersetCard 3 (Finset.Icc 1 9)) := by
      ext x
      simp
      tauto
    rw [this]
    rw [Set.ncard_coe_Finset]
    native_decide