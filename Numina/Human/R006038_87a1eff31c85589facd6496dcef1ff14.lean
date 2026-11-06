import Mathlib
open Nat

/-Eight strangers are preparing to play bridge. How many ways can they be grouped into two bridge games - that is, into unordered pairs of unordered pairs of people?
-/

-- Theorem showing the number of ways to partition 2k items into k unordered pairs using factorials.
def ways_to_form_k_pairs (k : ℕ) : ℕ :=
  (factorial (2*k)) / (factorial k * (2^k))

lemma ways_to_pair_8_people_val : ways_to_form_k_pairs 4 = 105 := by
  unfold  ways_to_form_k_pairs
  -- (factorial (2*4)) / (factorial 4 * (2^4))
  -- (factorial 8) / (factorial 4 * 16)
  -- 40320 / (24 * 16) = 40320 / 384 = 105
  rw [show 2*4 = 8 by norm_num, show 2^4 = 16 by norm_num]
  rfl

-- Number of ways to group 4 distinct pairs into 2 unordered pairs of pairs.
-- Using the formula with k=2.

lemma ways_to_group_4_pairs_val : ways_to_form_k_pairs 2 = 3 := by
  unfold ways_to_form_k_pairs
  -- (factorial (2*2)) / (factorial 2 * (2^2))
  -- (factorial 4) / (factorial 2 * 4)
  -- 24 / (2 * 4) = 24 / 8 = 3
  rw [show 2*2 = 4 by norm_num, show 2^2 = 4 by norm_num]
  rfl


theorem combinatorics_611227 : ways_to_form_k_pairs 4 * ways_to_form_k_pairs 2 = 315 := by
  rw [ways_to_pair_8_people_val, ways_to_group_4_pairs_val]

