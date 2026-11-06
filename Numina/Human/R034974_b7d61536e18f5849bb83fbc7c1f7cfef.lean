import Mathlib

open Finset

/-On considère 5 nombres entiers positifs. En les ajoutant deux à deux de toutes les façons possibles, on génère 10 entiers. Montrer que ces 10 entiers ne peuvent pas être 10 entiers consécutifs.-/
theorem number_theory_607693 (a b c d e : ℕ) : ¬ ∃ n : ℕ,
    ({a + b, a + c, a + d, a + e, b + c, b + d, b + e, c + d, c + e, d + e} : Multiset ℕ) =
    (Icc n (n + 9)).val := by
-- Assuming the statement, we compute the sum of the elements of the two sets on both sides
  rintro ⟨n, hn⟩; apply_fun fun t => t.sum at hn
-- Simplify `hn`
  simp [show Icc n (n+9) = Ico n (n+10) by rfl] at hn
  rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left] at hn
  rw [sum_add_distrib, sum_range_id] at hn; simp at hn
-- Deduct a contradiction by modulo $2$
  ring_nf at hn; apply_fun fun t => t % 2 at hn; omega