import Mathlib

/-Jack, Jill, and John play a game in which each randomly picks and then replaces a card from a standard 52 card deck, until a spades card is drawn. What is the probability that Jill draws the spade? (Jack, Jill, and John draw in that order, and the game repeats if no spade is drawn.)-/

inductive GameSuit : Type
| diamond | heart | club | spade
deriving Repr, Fintype, DecidableEq 

def deck_suits : Multiset GameSuit :=
  Multiset.replicate 13 GameSuit.diamond +
  Multiset.replicate 13 GameSuit.heart +
  Multiset.replicate 13 GameSuit.club +
  Multiset.replicate 13 GameSuit.spade

-- Lemma to confirm the total number of "cards" (suits) in the deck
lemma deck_suits_card_eq_52 : deck_suits.card = 52 := by
  simp [deck_suits] -- Unfold definition 

-- Lemma to confirm the number of spades in the deck
lemma deck_suits_count_spade_eq_13 : Multiset.count GameSuit.spade deck_suits = 13 := by
  simp [deck_suits, Multiset.count_add, Multiset.count_replicate]  

-- Probability of drawing a spade, derived from the deck model
noncomputable def p_spade : ℝ := (Multiset.count GameSuit.spade deck_suits : Rat) / (deck_suits.card : ℝ)

-- Probability of not drawing a spade
noncomputable def p_not_spade : ℝ := 1 - p_spade

-- Lemma to establish the numerical value of p_spade
lemma p_spade_value : p_spade = (1:ℝ)/4 := by
  simp [p_spade, deck_suits_card_eq_52, deck_suits_count_spade_eq_13] -- Substitute known counts
  norm_num -- Calculate 13/52 = 1/4

-- Lemma to establish the numerical value of p_not_spade
lemma p_not_spade_value : p_not_spade = (3:ℝ)/4 := by
  simp [p_not_spade, p_spade_value] -- Substitute value of p_spade
  norm_num -- Calculate 1 - 1/4 = 3/4

-- Probabilities for each player winning in a single round where the game ends
noncomputable def p_Jack_wins_round : ℝ := p_spade
noncomputable def p_Jill_wins_round : ℝ := p_not_spade * p_spade
noncomputable def p_John_wins_round : ℝ := p_not_spade * p_not_spade * p_spade

-- Probability that the game ends in any given round (someone draws a spade)
noncomputable def p_game_ends_in_round : ℝ :=
  p_Jack_wins_round +
  p_Jill_wins_round +
  p_John_wins_round

-- Your theorem name and statement
theorem combinatorics_608154 :
    p_Jill_wins_round / p_game_ends_in_round = (12:ℝ) / 37 := by
  -- Unfold the definitions of the round probabilities
  unfold p_game_ends_in_round p_Jack_wins_round p_John_wins_round p_Jill_wins_round

  -- Substitute the numerical values of p_spade and p_not_spade
  rw [p_spade_value, p_not_spade_value]

  -- Final numerical check
  norm_num

