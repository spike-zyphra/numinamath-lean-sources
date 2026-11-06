import Mathlib

theorem algebra_290712 {a : ℕ → ℝ} (ha1 : a 1 = 1 / 2)
    (han : ∀ n ≥ 1, a (n + 1) = (1 + a n) / (1 - a n)) :
    a 2008 = -1 / 3 := by

  -- Compute the next few terms to find a cycle
  have ha2 : a 2 = 3 := by
    rw [han 1 (by norm_num), ha1]
    norm_num

  have ha3 : a 3 = -2 := by
    rw [han 2 (by norm_num), ha2]
    norm_num

  have ha4 : a 4 = -1 / 3 := by
    rw [han 3 (by norm_num), ha3]
    norm_num

  -- Prove by induction that every 4 terms, the value is -1/3
  have h1 : ∀ k, a (4 * k + 4) = -1 / 3 := by
    intro k
    induction k with
    | zero =>
      norm_num [ha4]
    | succ k ih =>
      have eq1 : a (4 * k + 5) = 1 / 2 := by
        rw [han (4 * k + 4) (by omega)]
        rw [ih]
        norm_num
      -- Compute a(4k+6) = 3
      have eq2 : a (4 * k + 6) = 3 := by
        rw [han (4 * k + 5) (by omega)]
        rw [eq1]
        norm_num
      -- Compute a(4k+7) = -2
      have eq3 : a (4 * k + 7) = -2 := by
        rw [han (4 * k + 6) (by omega)]
        rw [eq2]
        norm_num
      -- Compute a(4k+8) = -1/3
      have eq4 : a (4 * k + 8) = -1 / 3 := by
        rw [han (4 * k + 7) (by omega)]
        rw [eq3]
        norm_num
      -- Simplify the index
      have eq5 : 4 * (k + 1) + 4 = 4 * k + 8 := by
        omega
      rw [eq5]
      exact eq4

  -- Now apply the formula for the specific term 2008
  have h2008 : a 2008 = -1 / 3 := by
    have h2008 := h1 501
    norm_num at h2008 ⊢
    all_goals linarith

  exact h2008