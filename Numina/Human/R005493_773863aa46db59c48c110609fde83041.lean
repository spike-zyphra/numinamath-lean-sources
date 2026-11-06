import Mathlib

/-How many sequences of 5 positive integers $(a, b, c, d, e)$ satisfy $a b c d e \leq a+b+c+d+e \leq 10$ ?-/

-- Define the finite range for each integer in the sequence.
abbrev value_range : Finset ℕ := Finset.Icc 1 6

-- The sample space Ω is the 5-fold cartesian product of this range.
-- This creates all possible sequences (a,b,c,d,e) to check.
def Ω : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  Finset.product value_range <|
  Finset.product value_range <|
  Finset.product value_range <|
  Finset.product value_range value_range

-- Helper function to destructure the nested pairs from Finset.product.
def to_list (t : ℕ × ℕ × ℕ × ℕ × ℕ) : List ℕ :=
  [t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2]

-- Define the set of sequences `E` that satisfy the problem's conditions.
def E : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  Ω.filter (fun t =>
    let l := to_list t
    let sum := l.sum
    let prod := l.prod
    prod ≤ sum ∧ sum ≤ 10)

theorem num_sequences_is_116 : E.card = 116 := by native_decide

