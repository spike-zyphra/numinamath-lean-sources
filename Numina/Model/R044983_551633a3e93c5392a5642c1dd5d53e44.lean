import Mathlib

theorem number_theory_282340_set_eq : 
  {p : ℕ | p.Prime ∧ p < 200}.encard = 46 ∧ 
  {sum : ℕ | sum = ∑ p in (Finset.Ico 1 200).filter Nat.Prime, p} = {4227} := by
  have h1 : {p : ℕ | p.Prime ∧ p < 200} = Finset.filter (fun p => p.Prime ∧ p < 200) (Finset.Ico 0 200) := by
    ext p
    simp
    <;> omega
  have h2 : {p : ℕ | p.Prime ∧ p < 200}.encard = 46 := by
    rw [h1]
    rw [Set.encard_coe_eq_coe_finsetCard]
    native_decide
  have h3 : {sum : ℕ | sum = ∑ p in (Finset.Ico 1 200).filter Nat.Prime, p} = {4227} := by 
    ext sum
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor 
    · -- Assume sum = ∑ p in (Finset.Ico 1 200).filter Nat.Prime, p, prove sum = 4227
      intro h 
      rw [h] 
      native_decide
    · -- Assume sum = 4227, prove sum = ∑ p in (Finset.Ico 1 200).filter Nat.Prime, p
      intro h 
      rw [h] 
      native_decide
  constructor 
  · exact h2 
  · exact h3