import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_75601 {f : ℝ → ℝ} (hf : f = λ x => x ^ 2 + 6 * x + 7) :
    IsLeast {y | ∃ x, y = f (f (f (f x)))} 23 := by
  constructor 
  · -- First part of IsLeast: Show 23 is in the set.
    use -3
    norm_num [hf]
  · -- Second part of IsLeast: Show no value less than 23 is in the set.
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hx]
    norm_num [hf]
    nlinarith [sq_nonneg (x + 3), sq_nonneg (x ^ 2 + 6 * x + 7 + 2), sq_nonneg ((x ^ 2 + 6 * x + 7) + 2), sq_nonneg ((x ^ 2 + 6 * x + 7) ^ 2 + 6 * (x ^ 2 + 6 * x + 7) + 7 + 1)]