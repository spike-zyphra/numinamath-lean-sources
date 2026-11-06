import Mathlib

open Real
open scoped BigOperators

theorem inequalities_322653 (n : ℕ) (hn : 0 < n) :
  ∑ i in Finset.Icc 1 n, (1 / (i * (i + 2) : ℝ)) < 3 / 4 := by
  have h5 : ∀ n : ℕ, ∑ i in Finset.Icc 1 n, (1 / (i * (i + 2) : ℝ)) = 3 / 4 - (1 / 2) * (1 / (n + 1 : ℝ) + 1 / (n + 2 : ℝ)) := by 
    intro n 
    induction n with 
    | zero =>
      simp 
      <;> norm_num 
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      field_simp 
      ring 
  have h6 : ∑ i in Finset.Icc 1 n, (1 / (i * (i + 2) : ℝ)) < (3 / 4 : ℝ) := by
    have h7 : ∀ n : ℕ, ∑ i in Finset.Icc 1 n, (1 / (i * (i + 2) : ℝ)) = 3 / 4 - (1 / 2) * (1 / (n + 1 : ℝ) + 1 / (n + 2 : ℝ)) := h5 
    specialize h7 n
    have h8 : 0 < (1 / 2 : ℝ) * (1 / (n + 1 : ℝ) + 1 / (n + 2 : ℝ)) := by
      have hn1 : (n + 1 : ℝ) > 0 := by
        have hn1 : n + 1 > 0 := by omega
        exact_mod_cast hn1
      have hn2 : (n + 2 : ℝ) > 0 := by
        have hn2 : n + 2 > 0 := by omega
        exact_mod_cast hn2
      have h9 : 0 < (1 / (n + 1 : ℝ) + 1 / (n + 2 : ℝ)) := by
        positivity 
      nlinarith 
    linarith [h7] 
  exact_mod_cast h6