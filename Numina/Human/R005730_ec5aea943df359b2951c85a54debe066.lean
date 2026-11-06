import Mathlib
open Finset

/-Allen and Brian are playing a game in which they roll a 6 -sided die until one of them wins. Allen wins if two consecutive rolls are equal and at most 3 . Brian wins if two consecutive rolls add up to 7 and the latter is at most 3 . What is the probability that Allen wins?-/

-- Represents a die roll value (1 to 6)
-- We'll use Fin 6, where .val is 0 to 5, and map it to 1 to 6.
abbrev dieRollVal (r : Fin 6) : ℕ := r.val + 1

-- The set of all possible next rolls (as Fin 6 objects)
def all_next_rolls : Finset (Fin 6) := univ

lemma card_all_next_rolls : all_next_rolls.card = 6 := by
  simp [all_next_rolls, card_fin]

  -- DecidablePred fun r => is_next_roll_low (dieRollVal r)

-- Conditions for winning
def is_allen_win (prev_roll_val r2_val : ℕ) : Prop :=
  prev_roll_val = r2_val ∧ prev_roll_val ≤ 3

def is_brian_win (prev_roll_val r2_val : ℕ) : Prop :=
  prev_roll_val + r2_val = 7 ∧ r2_val ≤ 3

-- Predicates for next roll being low or high
def is_next_roll_low (r2_val : ℕ) : Prop := r2_val ≥ 1 ∧ r2_val ≤ 3
def is_next_roll_high (r2_val : ℕ) : Prop := r2_val ≥ 4 ∧ r2_val ≤ 6

instance a_win_decidable : DecidablePred fun r2 => is_allen_win prev_roll_val (dieRollVal r2) := by unfold is_allen_win; infer_instance

-- Number of next rolls r2 where Allen wins, given previous roll prev_roll_val
def num_allen_wins_now (prev_roll_val : ℕ) : ℕ :=
  (all_next_rolls.filter (fun r2 : Fin 6 => is_allen_win prev_roll_val (dieRollVal r2))).card

instance b_win_decidable : DecidablePred fun r2 => is_brian_win prev_roll_val (dieRollVal r2) := by unfold is_brian_win; infer_instance

-- Number of next rolls r2 where Brian wins, given previous roll prev_roll_val
def num_brian_wins_now (prev_roll_val : ℕ) : ℕ :=
  (all_next_rolls.filter (fun r2 : Fin 6 => is_brian_win prev_roll_val (dieRollVal r2))).card

instance :  DecidablePred fun r2 =>
    ¬is_allen_win prev_roll_val (dieRollVal r2) ∧
      ¬is_brian_win prev_roll_val (dieRollVal r2) ∧ is_next_roll_low (dieRollVal r2)
  := by unfold is_allen_win is_brian_win is_next_roll_low; infer_instance

-- Number of next rolls r2 where game continues and next roll is Low (1,2,3)
def num_continue_next_low (prev_roll_val : ℕ) : ℕ :=
  (all_next_rolls.filter (fun r2 : Fin 6 =>
    ¬(is_allen_win prev_roll_val (dieRollVal r2)) ∧
    ¬(is_brian_win prev_roll_val (dieRollVal r2)) ∧
    is_next_roll_low (dieRollVal r2)
  )).card

instance :  DecidablePred fun r2 =>
      ¬is_allen_win prev_roll_val (dieRollVal r2) ∧
      ¬is_brian_win prev_roll_val (dieRollVal r2) ∧ is_next_roll_high (dieRollVal r2)
  := by unfold is_allen_win is_brian_win is_next_roll_high; infer_instance

-- Number of next rolls r2 where game continues and next roll is High (4,5,6)
def num_continue_next_high (prev_roll_val : ℕ) : ℕ :=
  (all_next_rolls.filter (fun r2 : Fin 6 =>
    ¬(is_allen_win prev_roll_val (dieRollVal r2)) ∧
    ¬(is_brian_win prev_roll_val (dieRollVal r2)) ∧
    is_next_roll_high (dieRollVal r2)
  )).card


def num_first_roll_is_low : ℕ :=
haveI :   DecidablePred fun r => is_next_roll_low (dieRollVal r) := by unfold is_next_roll_low; infer_instance
  (all_next_rolls.filter (fun r : Fin 6 => is_next_roll_low (dieRollVal r))).card

def num_first_roll_is_high : ℕ := 
  haveI : DecidablePred fun r => is_next_roll_high (dieRollVal r) := by unfold is_next_roll_high; infer_instance
  (all_next_rolls.filter (fun r : Fin 6 => is_next_roll_high (dieRollVal r))).card

lemma card_first_roll_is_low : num_first_roll_is_low = 3 := by native_decide
lemma card_first_roll_is_high : num_first_roll_is_high = 3 := by native_decide


-- Probabilities p and q (Allen wins if previous roll was low/high)
variable (p q : ℚ)

-- Definition of the overall probability that Allen wins
def P_Allen_wins_def : ℚ :=
  (num_first_roll_is_low / 6) * p + (num_first_roll_is_high / 6) * q

theorem combinatorics_609623 :
  P_Allen_wins_def (1/2) (1/3) = (5 : ℚ) / 12 := by
  simp [P_Allen_wins_def, card_first_roll_is_low, card_first_roll_is_high]
  ring
