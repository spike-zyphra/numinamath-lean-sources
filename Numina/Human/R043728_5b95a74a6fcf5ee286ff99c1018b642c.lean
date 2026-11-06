import Mathlib

/-
What is the probability that a randomly drawn positive factor of $60$ is less than $7$?
-/

-- In order to simplify the formalization, we can restate the problem without involving probability theory.
-- Notice that probability = number of positive factors of 60 less than 7 / number of positive factors of 60

-- First, prove that $ { k ∈ (60).divisors | k < 7 } $ is finite to be able to speak about its cardinal
local instance : Fintype { k ∈ (60).divisors | k < 7 } :=
  Set.fintypeSubset (60).divisors (Set.sep_subset ..)

theorem number_theory_1144 :
    { k ∈ (60).divisors | k < 7 }.toFinset.card / (60).divisors.card = (1 : ℝ) / 2 := by

  -- Determine the prime factors of 60, by successive divisions
  replace : 60 % 2 = 0 := by norm_num -- The first factor is 2
  replace : 60 / 2 = 30 := by norm_num
  replace : 30 % 2 = 0 := by norm_num -- The next factor is 2
  replace : 30 / 2 = 15 := by norm_num
  replace : 15 % 2 ≠ 0 := by norm_num
  replace : 15 % 3 = 0 := by norm_num -- The next factor is 3
  replace : 15 / 3 = 5 := by norm_num
  replace : 5 % 3 ≠ 0 := by norm_num
  replace : 5 % 4 ≠ 0 := by norm_num
  replace : 5 % 5 = 0 := by norm_num -- The next factor is 5
  replace : 5 / 5 = 1 := by norm_num

  -- The prime factorization is $ 60 = 2^2 * 3^1 * 5^1 $
  replace : 60 = 2^2 * 3^1 * 5^1 := by norm_num

  -- Therefore the number of divisors of 60 must be $ (2 + 1) * (1 + 1) * (1 + 1) = 3 * 2 * 2 = 12 $
  have h1 : (60).divisors.card = 12 := by decide

  -- Find the positive divisors of 60 less than 7
  replace : 60 % 1 = 0 := by norm_num -- 1 works
  replace : 60 % 2 = 0 := by norm_num -- 2 works
  replace : 60 % 3 = 0 := by norm_num -- 3 works
  replace : 60 % 4 = 0 := by norm_num -- 4 works
  replace : 60 % 5 = 0 := by norm_num -- 5 works
  replace : 60 % 6 = 0 := by norm_num -- 6 works

  -- There are 6 divisors of 60 less than 7
  have h2 : { k ∈ (60).divisors | k < 7 }.toFinset.card = 6 := by
    -- Rewrite as an intersection, so that decide can check the equality
    have : { k ∈ (60).divisors | k < 7 } = (60).divisors ∩ Finset.Ico 0 7 := by
      ext k
      simp
    simp only [this]
    decide

  -- Therefore the answer must be $ 6 / 12 = 1 / 2 $
  simp only [h1, h2]
  norm_num