import Mathlib

open Finset

theorem algebra_237041 {f : ℕ → ℝ → ℝ} (hf1 : ∀ x, f 1 x = -(2 * x + 7) / (x + 3))
    (hfn : ∀ n > 0, f (n + 1) = f 1 ∘ f n) :
    f 2022 2021 = 2021 := by

  -- Show that for all n, f(3n+3)(2021) = 2021
  have h1 : ∀ (n : ℕ), f (3 * n + 3) 2021 = 2021 := by
    intro n
    induction n with
    | zero =>
      norm_num [Function.comp_apply, hfn, hf1]
    | succ n ih =>
      have eq1 : f (3 * (n + 1) + 3) 2021 = f 1 (f (3 * n + 3 + 2) 2021) := by
        rw [show 3 * (n + 1) + 3 = (3 * n + 3 + 2) + 1 by omega]
        rw [hfn (3 * n + 3 + 2) (by omega)]
        all_goals simp [Function.comp_apply]
      have eq2 : f (3 * n + 3 + 2) 2021 = f 1 (f (3 * n + 3 + 1) 2021) := by
        rw [show 3 * n + 3 + 2 = (3 * n + 3 + 1) + 1 by omega]
        rw [hfn (3 * n + 3 + 1) (by omega)]
        all_goals simp [Function.comp_apply]
      have eq3 : f (3 * n + 3 + 1) 2021 = f 1 (f (3 * n + 3) 2021) := by
        rw [show 3 * n + 3 + 1 = (3 * n + 3) + 1 by omega]
        rw [hfn (3 * n + 3) (by omega)]
        all_goals simp [Function.comp_apply]
      rw [eq1, eq2, eq3, ih]
      norm_num [Function.comp_apply, hfn, hf1]

  -- Now using the lemma for n = 673, we get f(2022)(2021) = 2021
  have h2 : f 2022 2021 = 2021 := by
    specialize h1 673
    norm_num at h1 ⊢
    linarith

  exact h2