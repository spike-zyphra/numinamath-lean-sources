import Mathlib

open Finset

theorem algebra_211385 {f : ℕ → ℝ → ℝ}
    (hf0 : ∀ x, f 0 x = 1 / (1 - x))
    (hfn : ∀ n > 0, ∀ x, f n x = f 0 (f (n - 1) x)) :
    f 2011 2011 = 2010 / 2011 := by
  have h1 : ∀ (n : ℕ), f (3 * n + 1) 2011 = (2011 - 1) / 2011 := by
    intro n
    induction n with
    | zero =>
      norm_num [hfn, hf0]
    | succ n ih =>
      have eq1 : f (3 * (n + 1) + 1) 2011 = f (3 * n + 4) 2011 := by 
        ring_nf 
      rw [eq1]
      have eq2 : f (3 * n + 4) 2011 = f 0 (f (3 * n + 3) 2011) := by 
        apply hfn 
        all_goals 
          norm_num 
      have eq3 : f (3 * n + 3) 2011 = f 0 (f (3 * n + 2) 2011) := by 
        apply hfn 
        all_goals 
          omega 
      have eq4 : f (3 * n + 2) 2011 = f 0 (f (3 * n + 1) 2011) := by 
        apply hfn 
        all_goals 
          omega 
      rw [eq2, eq3, eq4, ih]
      norm_num [hf0]
  have h2011 : f 2011 2011 = (2011 - 1) / 2011 := by 
    have h2 : ∀ (n : ℕ), f (3 * n + 1) 2011 = (2011 - 1) / 2011 := h1
    specialize h2 670
    norm_num at h2 ⊢ 
    <;> linarith 
  linarith [h2011]