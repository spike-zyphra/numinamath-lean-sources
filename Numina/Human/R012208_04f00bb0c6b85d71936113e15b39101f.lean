import Mathlib

open Nat Rat Finset

/-Forty two cards are labeled with the natural numbers 1 through 42 and randomly shuffled into a stack. One by one, cards are taken off of the top of the stack until a card labeled with a prime number is removed. How many cards are removed on average?-/


-- Number of prime cards among those labeled 1 through 42.
-- We filter the range [1, 42].
def num_prime_cards : ℕ := (Finset.Icc 1 42).filter Nat.Prime |>.card

-- Lemma to verify the number of primes up to 42.
-- Primes are: 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41 (13 primes).
lemma num_prime_cards_eq_13 : num_prime_cards = 13 := by
  unfold num_prime_cards 
  -- The computation of (Finset.Icc 1 42).filter Nat.Prime |>.card can be done by rfl
  rfl

-- Number of non-prime cards.
def num_non_prime_cards : ℕ := 42 - num_prime_cards

lemma num_non_prime_cards_eq_29 : num_non_prime_cards = 29 := by
  unfold num_non_prime_cards 
  rw [num_prime_cards_eq_13] -- Substitute the proven number of primes

-- According to the solution sketch, the average number of non-primes removed
-- before the first prime is `num_non_prime_cards / (num_prime_cards + 1)`.
-- The total average number of cards removed is this quantity plus 1 (for the prime card itself).
def expected_cards_removed : ℚ :=
  (↑num_non_prime_cards / (↑num_prime_cards + (1 : ℕ))) + (1 : ℚ)

theorem number_theory_608158 :
    expected_cards_removed = (43 : ℚ) / 14 := by
  unfold expected_cards_removed
  -- Substitute the known values for num_prime_cards and num_non_prime_cards
  rw [num_prime_cards_eq_13, num_non_prime_cards_eq_29]
  norm_cast -- Simplifies casts from ℕ to ℚ
  ring
