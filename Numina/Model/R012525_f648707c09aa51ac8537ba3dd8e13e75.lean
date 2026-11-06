import Mathlib

theorem algebra_238082 {x : ℕ → ℝ} (hx1 : x 1 = 6) (hxn : ∀ n ≥ 2, x n = x (n - 1) / 5 + 4) :
    x 2017 = 5 + 1 / 5 ^ 2016 := by
  have h1 : ∀ n : ℕ, x (n + 1) = 5 + 1 / 5 ^ n := by
    intro n 
    induction n with
    | zero =>
      have eq1 : x (0 + 1) = 5 + 1 / 5 ^ (0 : ℕ) := by
        have h1' : x 1 = 6 := hx1
        norm_num at h1' ⊢ 
        all_goals linarith
      exact_mod_cast eq1
    | succ k ih =>
      have h2 : x ((k + 1) + 1) = x (k + 1) / 5 + 4 := by
        specialize hxn ((k + 1) + 1) (by linarith)
        simpa using hxn
      rw [h2, ih]
      field_simp
      <;> ring_nf
      all_goals norm_num
      all_goals try linarith
  specialize h1 2016
  simpa using h1