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
  have h1 : { k ∈ (60).divisors | k < 7 }.toFinset.card = 6 := by
    native_decide
  have h2 : (60).divisors.card = 12 := by
    native_decide
  rw [h1, h2]
  norm_num