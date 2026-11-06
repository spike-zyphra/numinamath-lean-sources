import Mathlib

open Nat 

def C (n k : Nat) : Nat := Nat.choose n k

/-
Theorem to solve the problem related to the occurrences of 3003 in Pascal's triangle
-/
theorem Pascal_Triangle :
    ∃ (a b : ℕ), 
    C a 2 = 3003 ∧ C 15 b = 3003 ∧ a + b * (15 - b) = 128 
    := by

  -- Specify the candidates for a and b: a = 78, b = 5
  use 78, 5  

 -- Start proving the conjunction by breaking it into parts
  constructor 
  
  -- First, prove that C 78 2 = 3003
  simp [C, Nat.choose_succ_succ, Nat.choose_succ_succ, Nat.choose_succ_succ, Nat.choose_succ_succ]
  norm_num
  constructor 
  


