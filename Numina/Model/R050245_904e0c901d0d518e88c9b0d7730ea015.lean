import Mathlib

theorem algebra_286084 {a : ℕ → ℝ} (ha1 : a 1 = 3)
    (han : ∀ n, a (n + 1) = -1 / (a n + 1)) : a 2008 = 3 := by 
  have ha2 : a 2 = -1 / 4 := by
    rw [han 1, ha1]
    norm_num
  have ha3 : a 3 = -4 / 3 := by
    rw [han 2, ha2]
    norm_num
  have ha4 : a 4 = 3 := by
    rw [han 3, ha3]
    norm_num
  have h : ∀ k, a (3 * k + 1) = 3 := by
    intro k 
    induction k with
    | zero =>
      norm_num [ha1]
    | succ k ih =>
      have h2 : a (3 * k + 2) = -1 / 4 := by 
        rw [han (3 * k + 1), ih]
        norm_num
      have h3 : a (3 * k + 3) = -4 / 3 := by 
        rw [han (3 * k + 2), h2]
        norm_num
      have h4 : a (3 * (k + 1) + 1) = 3 := by
        rw [show 3 * (k + 1) + 1 = (3 * k + 3) + 1 by ring]
        rw [han (3 * k + 3), h3]
        norm_num
      simpa using h4
  have : 2008 = 3 * 669 + 1 := by norm_num
  rw [this]
  apply h
  all_goals norm_num
  <;> try { norm_num [ha1] }