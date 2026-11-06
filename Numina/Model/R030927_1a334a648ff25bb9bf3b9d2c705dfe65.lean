import Mathlib

open Finset

theorem other_54935 {f : ℕ → ℕ} (hf1 : f 1 = 2) (hfn : ∀ n > 1, (Even n → f n = f (n - 1) + 1) ∧ (Odd n → f n = f (n - 2) + 2)) : f 2017 = 2018 := by
  have h1 : ∀ (n : ℕ), f (2 * n + 1) = 2 * n + 2 := by
    intro n
    induction n with 
    | zero => 
      simp [hf1] 
    | succ n ih => 
      have h11 : f (2 * (n + 1) + 1) = f (2 * n + 1) + 2 := by 
        have eq2 : (2 * (n + 1) + 1 : ℕ) = (2 * n + 3 : ℕ) := by omega 
        rw [eq2] 
        have h4 : Odd (2 * n + 3 : ℕ) := by 
          use n + 1 
          all_goals omega 
        have h6 := (hfn (2 * n + 3) (by omega)).2 
        have eq8 : (2 * n + 3 - 2 : ℕ) = (2 * n + 1 : ℕ) := by omega 
        rw [eq8] at h6 
        have hx := h6 h4 
        simpa using hx 
      rw [h11] 
      rw [ih] 
      all_goals omega 
  have h2017 := h1 1008 
  norm_num at h2017 ⊢ 
  all_goals omega