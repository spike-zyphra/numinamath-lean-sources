import Mathlib

def isLose (n : ℕ) : Prop :=
  n.divisors.card = 6 ∧ ∀ a ∈ n.divisors, ∀ b ∈ n.divisors, a < b → b ≥ 2 * a

theorem number_theory_610441 :
    ∑ᶠ n ∈ {n | n < 100 ∧ isLose n}, n = 512 := by

  have h1 : {n | n < 100 ∧ isLose n} = 
    Finset.filter (fun n => n.divisors.card = 6 ∧ ∀ a ∈ n.divisors, ∀ b ∈ n.divisors, a < b → b ≥ 2 * a) (Finset.Ico (0 : ℕ) 100) := by
    ext n
    simp [isLose]
    <;> try tauto

  rw [h1]
  rw [finsum_mem_coe_finset]
  native_decide