import Mathlib
set_option maxHeartbeats 0

open Finset

/-To celebrate 2019, Faraz gets four sandwiches shaped in the digits 2, 0, 1, and 9 at lunch. However, the four digits get reordered (but not flipped or rotated) on his plate and he notices that they form a 4-digit multiple of 7 . What is the greatest possible number that could have been formed?
-/
theorem number_theory_610105 : IsGreatest {n : ℕ | ∃ a b c d, Nat.digits 10 n = [d, c, b, a]
    ∧ ({a, b, c, d} : Finset ℕ) = {2, 0, 1, 9} ∧ 7 ∣ n} 1092 := by
  simp [IsGreatest, upperBounds]; constructor
  -- Check that $1092$ indeed satisfies the required properties
  · use 1, 0, 9, 2; norm_num [Finset.ext_iff]
    intro; omega
-- To show that $1092$ is an upper bounds, we first show that $a$, $b$, $c$ and $d$ are pairwise distinct
  intro n a b c d hn hdig hdvd
  let aux := hdig; apply_fun fun t => #t at aux
  simp at aux; repeat rw [card_insert_eq_ite] at aux
  split_ifs at aux; all_goals simp at aux
  rename_i ne1 ne2 ne3; simp at ne1 ne2 ne3
-- Prove that $a$ is nonzero
  have ane : a ≠ 0 := by
    have : a = [d, c, b, a].getLast (by simp) := by simp
    simp [← hn] at this
    rw [this]; apply Nat.getLast_digit_ne_zero
    intro h; simp [h] at hn
  let hn' := hn; apply_fun fun t => Nat.ofDigits 10 t at hn'
  rw [Nat.ofDigits_digits] at hn'
  simp [Nat.ofDigits_eq_sum_mapIdx] at hn'
  rw [hn']; rw [hn'] at hdvd
  simp [Finset.ext_iff] at hdig
  have ha := hdig a; have hb := hdig b
  have hc := hdig c; have hd := hdig d
  simp at ha hb hc hd
-- Check all possible values for $a$, $b$, $c$ and $d$
  rcases ha with _|_|_|_ <;> rcases hb with _|_|_|_ <;>
  rcases hc with _|_|_|_ <;> rcases hd with _|_|_|_
  all_goals simp_all
  all_goals norm_num at hdvd