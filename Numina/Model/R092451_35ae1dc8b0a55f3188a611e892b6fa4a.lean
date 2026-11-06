import Mathlib

theorem number_theory_186737 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1 100 ∧ n.divisors.card = 4 ∧
      ∃ s : Finset ℕ, s ⊆ n.divisors ∧ s.card ≥ 3 ∧ ∀ i ∈ s, i ≤ 10} = 8 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 100 ∧ n.divisors.card = 4 ∧
      ∃ s : Finset ℕ, s ⊆ n.divisors ∧ s.card ≥ 3 ∧ ∀ i ∈ s, i ≤ 10} = Finset.filter (fun n => n.divisors.card = 4 ∧
      ∃ s : Finset ℕ, s ⊆ n.divisors ∧ s.card ≥ 3 ∧ ∀ i ∈ s, i ≤ 10) (Finset.Icc 1 100) := by
    ext n
    simp
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide