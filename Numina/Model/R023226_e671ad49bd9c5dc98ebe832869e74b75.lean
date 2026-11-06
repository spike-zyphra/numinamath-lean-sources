import Mathlib

theorem algebra_125708 {f : ℕ → ℝ} (hf1 : f 1 = 1) (hfn : ∀ n ≥ 2, f n = f (n - 1) + 1 / (n * (n - 1))) :
    f 2019 = 4037 / 2019 := by

  have h1 : ∀ n : ℕ, f (n + 1) = (2 * (n + 1) - 1) / ((n + 1) : ℝ) := by
    intro n
    induction n with
    | zero =>
      norm_num
      all_goals
        norm_num [hf1]
    | succ n ih =>
      have eq1 : f ((n + 1 + 1) ) = f ((n + 1) ) + 1 / ((n + 1 + 1 ) * (n + 1) : ℝ ) := by
        specialize hfn (n + 1 + 1) (by linarith)
        simpa using hfn
      rw [eq1]
      rw [ih]
      field_simp
      ring

  have h2 : f 2019 = (2 * (2018 + 1) - 1) / ((2018 + 1) : ℝ) := by 
    specialize h1 2018
    norm_num at h1 ⊢
    linarith

  rw [h2]
  norm_num