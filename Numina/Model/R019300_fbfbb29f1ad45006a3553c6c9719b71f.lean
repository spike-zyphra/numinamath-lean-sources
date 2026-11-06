import Mathlib

open Finset Real

theorem algebra_225660 {f : ℝ → ℝ} (hf : f = fun x => 1 / (1 - x)) :
    f^[2005] 2005 = -1 / 2004 := by
  have h1 : ∀ (n : ℕ), f^[3 * n + 1] 2005 = -1 / 2004 := by
    intro n
    induction n with
    | zero =>
      norm_num [Function.iterate_succ_apply', hf]
    | succ n ih =>
      have h2 : f^[3 * (n + 1) + 1] 2005 = f^[3 * n + 1 + 3] 2005 := by
        ring_nf
      rw [h2]
      have h3 : f^[3 * n + 1 + 3] 2005 = f^[3 * n + 1] (f^[3] 2005) := by
        rw [Function.iterate_add_apply]
      rw [h3]
      have h4 : f^[3] 2005 = (2005 : ℝ) := by
        norm_num [Function.iterate_succ_apply', hf]
      rw [h4]
      all_goals try exact ih
  have h2 : (2005 : ℕ) = 3 * (668 : ℕ) + 1 := by
    norm_num
  rw [h2]
  apply h1