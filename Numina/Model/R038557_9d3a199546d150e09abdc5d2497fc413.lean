import Mathlib

theorem algebra_164336 {a : ℕ → ℝ} (ha1 : a 1 = 2)
    (han : ∀ n, a (n + 1) = (5 * a n - 13) / (3 * a n - 7)) :
    a 2011 = 2 := by
  have h1 : ∀ k : ℕ, a (3 * k + 1) = 2 := by 
    intro k 
    induction k with 
    | zero =>
      norm_num [ha1]
    | succ k ih =>
      have h2 : a (3 * k + 2) = 3 := by 
        rw [han (3 * k + 1)]
        rw [ih]
        norm_num 
      have h3 : a (3 * k + 3) = 1 := by 
        rw [han (3 * k + 2)]
        rw [h2]
        norm_num 
      have h4 : a (3 * (k + 1) + 1) = 2 := by
        have h5 : a (3 * k + 4) = 2 := by
          rw [han (3 * k + 3)]
          rw [h3]
          norm_num 
        have eq1 : 3 * (k + 1) + 1 = 3 * k + 4 := by
          omega 
        rw [eq1]
        exact h5 
      exact h4
  have eq2011 : 2011 = 3 * 670 + 1 := by 
    norm_num
  rw [eq2011]
  exact h1 670