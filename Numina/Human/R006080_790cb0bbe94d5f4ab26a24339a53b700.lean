import Mathlib

open Finset

/-
Fifteen freshmen are sitting in a circle around a table,
but the course assistant (who remains standing) has made only six copies of today's handout.
No freshman should get more than one handout, and any freshman who does not get one should be able to read a neighbor's.
If the freshmen are distinguishable but the handouts are not, how many ways are there to distribute the six handouts subject to the above conditions?
-/

-- Define the condition: no three consecutive freshmen are without handouts.
-- `handouts` is the set of freshmen (represented by their index in Fin n) who receive a handout.
def handout_condition_prop (n : Nat) (handouts : Finset (Fin n))[NeZero n] : Prop :=
  -- `no_handouts` is the set of freshmen without handouts.
  let no_handouts := (univ : Finset (Fin n)) \ handouts
  -- The condition: For every freshman `i`, it's NOT the case that
  -- `i`, `i+1`, and `i+2` are ALL in `no_handouts`.
  -- Addition on `Fin n` is modular, correctly handling the circular arrangement.
  ∀ i : Fin n, ¬ (i ∈ no_handouts ∧ (i + Fin.ofNat' n 1) ∈ no_handouts ∧ (i + 2) ∈ no_handouts)

instance decidable_handout_condition_prop (n : Nat) (handouts : Finset (Fin n)) [NeZero n] :
    Decidable (handout_condition_prop n handouts ) := by
  unfold handout_condition_prop
  exact Fintype.decidableForallFintype

-- Problem parameters
abbrev num_freshmen : Nat := 15
abbrev num_handouts : Nat := 6

-- Calculate the number of valid distributions
-- This involves:
-- 1. Getting all Finsets of (Fin num_freshmen) of size num_handouts.
--    (These are all possible ways to give handouts to `num_handouts` freshmen).
-- 2. Filtering these Finsets by our condition.
-- 3. Counting the number of Finsets that satisfy the condition.
def count_valid_distributions : Nat :=
  let all_possible_handout_sets :=
    (univ : Finset (Fin num_freshmen)).powersetCard num_handouts
  let valid_sets :=
    all_possible_handout_sets.filter (fun hs => handout_condition_prop num_freshmen hs)
  valid_sets.card

-- For each set, the condition loops 15 times, performing 3 set lookups.
-- So, roughly 5005 * 15 * 3 = 225,225 lookups.
theorem combinatorics_611448 :  count_valid_distributions = 125 := by native_decide
