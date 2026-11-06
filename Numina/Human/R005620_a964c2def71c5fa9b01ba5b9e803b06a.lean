import Mathlib

open Finset Nat

-- Define the types for h, m, s to easily manage their ranges
abbrev Hour : Type := Fin 24 -- 0 to 23
abbrev MinuteSecond : Type := Fin 60 -- 0 to 59

-- The predicate for a valid time (h,m,s) satisfying h+m=s
def IsValidTime (t : Hour × MinuteSecond × MinuteSecond) : Prop :=
  (t.1.val + t.2.1.val = t.2.2.val)

-- The set of all valid times
def ValidTimesSet : Finset (Hour × MinuteSecond × MinuteSecond) :=
  haveI : DecidablePred IsValidTime := by unfold IsValidTime; infer_instance
  Finset.filter IsValidTime Finset.univ

-- Helper function: For a given s_val (0-59), count pairs (h,m) such that
-- 0 ≤ h ≤ 23, 0 ≤ m ≤ 59, and h + m = s_val.
-- This is the number of h in [0,23] such that s_val - h is in [0,59].
-- i.e., h ∈ [max(0, s_val - 59), min(23, s_val)].
def count_hm_pairs_for_s (s_val : ℕ) : ℕ :=
  let lower_h := max 0 (if s_val < 59 then 0 else s_val - 59) -- s_val - 59, but capped at 0
  let upper_h := min 23 s_val
  if lower_h ≤ upper_h then upper_h - lower_h + 1 else 0

-- Lemma to verify count_hm_pairs_for_s for s in [0,23]
lemma count_hm_for_s_le_23 (s_val : ℕ) (hs0 : 0 ≤ s_val) (hs23 : s_val ≤ 23) :
    count_hm_pairs_for_s s_val = s_val + 1 := by
  unfold count_hm_pairs_for_s
  have s_val_lt_59 : s_val < 59 := by linarith
  simp only [s_val_lt_59, if_true, max_eq_left (Nat.zero_le _)] -- lower_h = 0
  simp only [min_eq_right hs23] -- upper_h = s_val
  simp only [ge_iff_le, zero_le', tsub_zero, add_left_inj, le_refl, if_true] -- 0 <= s_val is true

theorem combinatorics_609149 :
    ValidTimesSet.card = 1164 := by
    unfold ValidTimesSet IsValidTime
    native_decide
