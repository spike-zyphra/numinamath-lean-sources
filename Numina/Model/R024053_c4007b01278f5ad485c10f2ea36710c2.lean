import Mathlib

def isSpicy (n : ℕ) := n ∈ Finset.Icc 100 999 ∧ n = (Nat.digits 10 n).headI ^ 3 + (Nat.digits 10 n).tail.headI ^ 3 + (Nat.digits 10 n).tail.tail.headI ^ 3

theorem number_theory_89091 {n : ℕ} (hn : isSpicy n) (h : isSpicy (n + 1)) :
    n = 370 := by
  rcases hn with ⟨hn1, hn2⟩
  rcases h with ⟨hn3, hn4⟩
  rw [Finset.mem_Icc] at hn1 hn3
  rcases hn1 with ⟨hn1l, hn1u⟩
  rcases hn3 with ⟨hn3l, hn3u⟩
  interval_cases n <;> norm_num [isSpicy] at hn2 hn4 ⊢ <;> omega