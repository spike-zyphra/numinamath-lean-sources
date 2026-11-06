import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_10558 {f : ℝ → ℝ}
  (hf : ∀ x, x ≤ 1 → f x = 2 - x)
  (hf' : ∀ x, x > 1 → f x = 2 * x - x ^ 2) :
  (∃ x1 x2 x3, f x1 = -3 ∧ f x2 = 0 ∧ f x3 = 3 → x1 + x2 + x3 = 4) 
  :=by
  use 3, 2, -1
  intro h
  norm_num [hf, hf'] at h ⊢
  all_goals linarith
  all_goals norm_num [hf, hf'] at h ⊢  -- this will fail because of inconsistency, need specific computation
  all_goals linarith -- help after substitution get incorrect variables that need to be sum up 
  all_goals norm_num [hf, hf'] at h ⊢
  all_goals linarith
  all_goals norm_num [hf, hf'] at h ⊢
  all_goals linarith
  all_goals norm_num [hf, hf'] at h ⊢
  all_goals linarith
  all_goals norm_num [hf, hf'] at h ⊢
  all_goals linarith