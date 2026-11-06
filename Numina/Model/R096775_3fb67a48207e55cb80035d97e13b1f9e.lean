import Mathlib

open Nat

def sumOfDigits (n : ℕ) := (Nat.digits 10 n).sum

theorem number_theory_238465 :
    IsGreatest {n % sumOfDigits n | n ∈ Finset.Icc 10 99} 15 := by
  constructor
  · -- Show that 15 is obtainable, using 79 as the witness
    use 79
    norm_num [sumOfDigits]
  · -- Show that any element in the set is at most 15
    intro r
    rintro ⟨n, hn, rfl⟩
    rw [Finset.mem_Icc] at hn
    rcases hn with ⟨hn1, hn2⟩

    interval_cases n <;> norm_num [sumOfDigits]
    <;> try { omega }