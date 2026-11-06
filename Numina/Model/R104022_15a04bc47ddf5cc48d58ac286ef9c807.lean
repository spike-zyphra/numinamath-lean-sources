import Mathlib

theorem algebra_11823 (a : ℕ → ℝ) (ha1 : a 1 = 2) (han : ∀ n, a (n + 1) = (5 * a n - 13) / (3 * a n - 7)) :
    a 2011 = 2 := by
  have h1 : ∀ k : ℕ, a (3 * k + 1) = 2 := by
    intro k
    induction k with
    | zero =>
      norm_num [ha1]
    | succ k ih =>
      have h2 : a (3 * (k + 1) + 1) = a (3 * k + 4) := by
        ring_nf
      have ha2' : a (3 * k + 2) = 3 := by
        rw [han (3 * k + 1), ih]
        norm_num
      have ha3' : a (3 * k + 3) = 1 := by
        rw [han (3 * k + 2), ha2']
        norm_num
      have ha4' : a (3 * k + 4) = 2 := by
        rw [han (3 * k + 3), ha3']
        norm_num
      rw [h2]
      exact ha4'
  have h2 : 2011 = 3 * 670 + 1 := by
    norm_num
  rw [h2]
  apply h1
  all_goals norm_num