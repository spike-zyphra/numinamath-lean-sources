import Mathlib

-- 1. (2 points) In a row without spaces, all natural numbers from 999 to 1 are written in descending order: 999998 ...321. What digit is in the 2710th position of the resulting long number?


-- Convert natural number to digit list (from high to low)
def nat_to_digits (n : ℕ) : List ℕ :=
  if n = 0 then [0] else Nat.digits 10 n |>.reverse

-- Calculate number of digits of a natural number
def num_digits (n : ℕ) : ℕ := (nat_to_digits n).length

-- Generate descending sequence from 999 to 1
def descending_sequence : List ℕ :=
  List.range 999 |>.map (fun i => 999 - i)



-- Convert digit sequence to single digit list
def sequence_to_digit_list (seq : List ℕ) : List ℕ :=
  seq.flatMap nat_to_digits


-- Complete digit sequence: 999998997...321
def full_digit_sequence : List ℕ :=
  sequence_to_digit_list descending_sequence

-- Get the digit at position n in the sequence (1-indexed)
def digit_at_position (pos : ℕ) : Option ℕ := full_digit_sequence[pos]?


theorem number_theory_211440 : digit_at_position 2710 = some 9 := by
  -- Verified by computation
  native_decide
