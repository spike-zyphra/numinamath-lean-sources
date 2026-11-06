import Mathlib
open Nat Rat

/-
A 50 -card deck consists of 4 cards labeled " $i$ " for $i=1,2, \ldots, 12$ and 2 cards labeled " 13 ". If Bob randomly chooses 2 cards from the deck without replacement, what is the probability that his 2 cards have the same label?
-/

-- Number of ways to choose 2 cards from the 50
def total_possible_pairs : ℕ := Nat.choose 50 2

lemma total_possible_pairs_val : total_possible_pairs = 1225 := by
  unfold total_possible_pairs 
  -- Nat.choose 50 2 = (50 * 49) / (2 * 1) = 25 * 49 = 1225
  rfl    

-- Number of ways to choose 2 cards with the same label for labels 1 through 12.
-- For each of these 12 labels, there are 4 cards.
-- The number of ways to choose 2 cards from 4 is Nat.choose 4 2.
def favorable_pairs_labels_1_to_12 : ℕ :=
  12 * (Nat.choose 4 2)

lemma favorable_pairs_labels_1_to_12_val : favorable_pairs_labels_1_to_12 = 72 := by
  unfold favorable_pairs_labels_1_to_12
  have h_choose_4_2 : Nat.choose 4 2 = 6 := by rfl
  rw [h_choose_4_2]

-- Number of ways to choose 2 cards with the label 13.
-- There are 2 cards labeled 13.
-- The number of ways to choose 2 cards from 2 is Nat.choose 2 2.
def favorable_pairs_label_13 : ℕ :=
  Nat.choose 2 2

lemma favorable_pairs_label_13_val : favorable_pairs_label_13 = 1 := by
  unfold favorable_pairs_label_13
  norm_num 

-- Total number of favorable pairs (pairs of cards with the same label)
def total_favorable_pairs : ℕ :=
  favorable_pairs_labels_1_to_12 + favorable_pairs_label_13

lemma total_favorable_pairs_val : total_favorable_pairs = 73 := by
  unfold total_favorable_pairs
  rw [favorable_pairs_labels_1_to_12_val, favorable_pairs_label_13_val]

-- The probability that the two chosen cards have the same label
def probability_cards_have_same_label : ℚ :=
  (↑total_favorable_pairs : ℚ) / (↑total_possible_pairs : ℚ)

theorem combinatorics_609150 :
    probability_cards_have_same_label = (73 : ℚ) / 1225 := by
  unfold probability_cards_have_same_label
  -- Substitute the proven values of the numerator and denominator
  rw [total_favorable_pairs_val, total_possible_pairs_val]
  norm_cast -- Simplifies the casts from ℕ to ℚ

