import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_188582 {P : ℕ → ℝ → ℝ}
  (hP : ∀ x, P 0 x = 1 ∧ P 1 x = x ∧ P 2 x = x ^ 2 - 1)
  (hP' : ∀ n x, P (n + 1) x = x * P n x - P (n - 1) x) :
  ∃ s : Finset ℝ, s.card = 100 ∧ ∀ x ∈ s, P 100 x = 0 ∧ x ∈ Icc (-2) 2 := by
  -- Let's consider n=0:
  have h1 := hP' 0 0
  norm_num [hP] at h1
  all_goals linarith [h1, (hP 0).1, (hP 0).2.1, (hP 0).2.2]