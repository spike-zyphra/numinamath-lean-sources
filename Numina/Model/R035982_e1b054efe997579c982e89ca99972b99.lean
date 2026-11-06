import Mathlib

open Finset

theorem algebra_235071 {a : ℕ → ℤ} (ha1 : a 1 = -1)(ha : ∀ k≥1, a (k+1) = -1 - a k):
    a 1989 = -1 ∧ a 1990 = 0 := by

  have h1 : ∀ n, a (2 * n + 1) = -1 ∧ a (2 * n + 2) = 0 := by
    intro n
    induction n with
    | zero =>
      constructor
      · -- Show that a 1 = -1
        exact ha1
      · -- Show that a 2 = 0
        have ha2 : a 2 = -1 - a 1 := by
          specialize ha 1 (by norm_num)
          simpa using ha
        rw [ha2, ha1]
        all_goals norm_num
    | succ n ih =>
      have h1 : a (2 * (n + 1) + 1) = -1 := by
        have eq1 : 2 * (n + 1) + 1 = (2 * n + 2) + 1 := by
          omega
        rw [eq1]
        have eq2 : a ((2 * n + 2) + 1) = -1 - a (2 * n + 2) := by
          apply ha
          linarith 
        rw [eq2]
        have eq3 : a (2 * n + 2) = 0 := by 
          linarith [ih.right] 
        rw [eq3] 
        all_goals norm_num 
      have h2 : a (2 * (n + 1) + 2) = 0 := by 
        have eq1 : 2 * (n + 1) + 2 = (2 * (n + 1) + 1) + 1 := by 
          omega 
        rw [eq1] 
        have eq2 : a ((2 * (n + 1) + 1) + 1) = -1 - a (2 * (n + 1) + 1) := by 
          apply ha 
          omega 
        rw [eq2, h1] 
        all_goals norm_num 
      constructor 
      · exact h1 
      · exact h2
  
  have h2 : a 1989 = -1 := by 
    have h3 := (h1 994).left 
    norm_num at h3 ⊢ 
    all_goals linarith
  
  have h3 : a 1990 = 0 := by 
    have h4 := (h1 994).right 
    norm_num at h4 ⊢ 
    all_goals linarith
  
  exact ⟨h2, h3⟩