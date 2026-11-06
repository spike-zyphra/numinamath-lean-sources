import Mathlib

open Finset

theorem number_theory_163798 {f : ℕ → ℝ}
    (hf : ∀ n, f (n + 2) = f (n + 1) + f n)
    (hf1 : f 0 = 1) (hf2 : f 1 = 1) :
    ∀ a b : ℕ, 0 < a → 0 < b →
      (∀ n, min (f n / f (n - 1)) (f (n + 1) / f n) < a / b ∧
        a / b < max (f n / f (n - 1)) (f (n + 1) / f n)) → b ≥ f (n + 1) := by
  intro a b ha hb h
  have h0 := h 0
  norm_num [hf1, hf2] at h0
  all_goals
    linarith