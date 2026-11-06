import Mathlib

open Nat


/-- `τ(n)` denotes the number of positive integer divisors of `n`. -/
abbrev tau (n : ℕ) : ℕ :=
  n.divisors.card
/-- `φ(n)` denotes the number of positive integers that are less than or equal to `n` and relatively prime to `n`. -/
abbrev phi (n : ℕ) : ℕ :=
  totient n

/-- A positive integer `n` is good if `φ(n) + 4 τ(n) = n`. -/
def is_good (n : ℕ) : Prop :=
  phi n + 4 * tau n = n

instance is_good_decidable (n : ℕ) : Decidable (is_good n) := by
  simp [is_good, phi, tau, totient]
  infer_instance

lemma is_good_iff (n : ℕ) :
  is_good n ↔ n = 44 ∨ n = 56 ∨ n = 72 := by
  apply Iff.intro
  · sorry
  · intro h
    rcases h with h | h | h <;>
    simp [is_good, phi, tau, totient, h] <;>
    tauto

/-- Find the sum of all good positive integers `n`. -/
noncomputable def sum_of_good_integers : ℕ :=
  ∑' (n : ℕ), if is_good n then n else 0

theorem numbertheory_609555 :
  sum_of_good_integers = 172 := by
  simp [sum_of_good_integers]
  have : ∀ n, n ∉ ({44, 56, 72} : Finset ℕ ) → (λ n => if is_good n then n else 0) n = 0 := by
    intro n hn
    simp at hn
    rcases hn with ⟨ _, _,_ ⟩
    simp
    intro h
    replace h := (is_good_iff n).mp h
    simp_all
  apply tsum_eq_sum this
