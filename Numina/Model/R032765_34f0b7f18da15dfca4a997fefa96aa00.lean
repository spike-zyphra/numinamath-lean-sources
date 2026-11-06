import Mathlib
open Real

theorem inequalities_604205 
  (bs : ℕ → ℤ)
  (hb : ∀ n, 0 < bs n)
  (h1 : bs 1 = 1)
  (h : ∀ n, (bs n : ℝ) / (n ^ 2 : ℝ) > (bs (n + 1) : ℝ) / ((n + 1) ^ 2 : ℝ)) :
  ∃ r : ℝ, (∀ n, (bs n : ℝ) / (n ^ 2 : ℝ) ≥ r) ∧ 0 ≤ r ∧ r ≤ 1 / 2 :=
by 
  use 0
  constructor
  · -- Show that 0 is indeed a lower bound
    intro n 
    have h2 : (bs n : ℝ) > 0 := by 
      exact_mod_cast (hb n)
    have h3 : (bs n : ℝ) / (n ^ 2 : ℝ) ≥ 0 := by
      apply div_nonneg
      linarith
      all_goals positivity 
    linarith 
  constructor
  · -- Show that 0 ≤ 0
    norm_num 
  · -- Show that 0 ≤ 1 / 2 
    norm_num