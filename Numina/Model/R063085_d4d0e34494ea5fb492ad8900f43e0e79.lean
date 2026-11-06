import Mathlib

theorem number_theory_73334 :
    (Finset.Icc 1 100).card * (Nat.divisors 100).card = 900 ∧
    {p : ℕ × ℕ | p.1 ∈ Nat.divisors 100 ∧ p.2 ∈ Finset.Icc 1 100 ∧ p.1 ∣ p.2}.ncard = 217 := by
  constructor
  · -- Show that the total number of pairs is 900
    native_decide
  · -- Show that the number of favorable pairs is 217
    have h1 : {p : ℕ × ℕ | p.1 ∈ Nat.divisors 100 ∧ p.2 ∈ Finset.Icc 1 100 ∧ p.1 ∣ p.2} = Finset.filter (λ p => p.1 ∣ p.2) ((Nat.divisors 100) ×ˢ (Finset.Icc 1 100)) := by
      ext ⟨d, z⟩
      simp [Finset.mem_Icc, Finset.mem_product]
      <;> tauto
    rw [h1]
    rw [Set.ncard_coe_Finset]
    native_decide