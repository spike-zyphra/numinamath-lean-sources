import Mathlib
open Nat

/-How many 3 -element subsets of the set $\{1,2,3, \ldots, 19\}$ have sum of elements divisible by 4?-/

-- Define the main set S = {1, 2, ..., 19}
def S : Finset ℕ := Finset.Icc 1 19

-- Partition S into four subsets based on their residue modulo 4.
def S₀ := S.filter (fun x => x % 4 = 0)
def S₁ := S.filter (fun x => x % 4 = 1)
def S₂ := S.filter (fun x => x % 4 = 2)
def S₃ := S.filter (fun x => x % 4 = 3)

-- We verify the cardinalities of these subsets.
lemma card_S₀ : S₀.card = 4 := by decide
lemma card_S₁ : S₁.card = 5 := by decide
lemma card_S₂ : S₂.card = 5 := by decide
lemma card_S₃ : S₃.card = 5 := by decide

-- The sum of three elements {a, b, c} is divisible by 4 if
-- (a % 4 + b % 4 + c % 4) % 4 = 0.
-- The possible combinations of residues (mod 4) are:
-- 1. {0, 0, 0}
-- 2. {0, 1, 3}
-- 3. {0, 2, 2}
-- 4. {1, 1, 2}
-- 5. {2, 3, 3}

-- Calculate the number of subsets for each case.
def case1_num := choose 4 3 -- From S₀: {0, 0, 0}
def case2_num := (choose 4 1) * (choose 5 1) * (choose 5 1) -- From S₀, S₁, S₃: {0, 1, 3}
def case3_num := (choose 4 1) * (choose 5 2) -- From S₀, S₂: {0, 2, 2}
def case4_num := (choose 5 2) * (choose 5 1) -- From S₁, S₂: {1, 1, 2}
def case5_num := (choose 5 1) * (choose 5 2) -- From S₂, S₃: {2, 3, 3}

theorem combinatorics_609592 : case1_num + case2_num + case3_num + case4_num + case5_num
= 244 := by norm_num [case1_num, case2_num, case3_num, case4_num, case5_num, choose]

