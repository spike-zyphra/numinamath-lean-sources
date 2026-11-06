import Mathlib

theorem number_theory_261452 {k : ℕ} (hk : k ∈ Finset.Icc 10 99) :
    ∃ N, (Nat.digits 10 N).headI ≠ 0 ∧ (Nat.ofDigits 10 (List.tail (Nat.digits 10 N))) = k * (Nat.ofDigits 10 (List.tail (Nat.digits 10 N))) := by 
  use 1
  simp
  all_goals tauto
  <;> try { tauto }
  all_goals omega