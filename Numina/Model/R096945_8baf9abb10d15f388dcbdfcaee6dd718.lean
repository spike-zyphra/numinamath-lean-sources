import Mathlib

theorem number_theory_325372 (A : ℕ) (hA : A ∈ Finset.Icc 10 99) (hA1 : (Nat.digits 10 A).length = 2)
    (hA2 : (Nat.digits 10 A).toFinset.card = 2) (hA3 : 11111 * A % 100000 = 0) :
    (Nat.digits 10 (Nat.digits 10 A).toFinset.card).toFinset.card = 3456 := by
  rw [Finset.mem_Icc] at hA
  rcases hA with ⟨hA4, hA5⟩
  interval_cases A <;> norm_num at hA1 hA2 hA3 ⊢ <;> all_goals contradiction