import Mathlib

theorem algebra_287003 {a : ℕ → ℚ} (ha1 : a 1 = 2)
    (han : ∀ n ≥ 1, a (n + 1) = (1 + a n) / (1 - a n)) :
    30 * a 2008 = 10 := by

  have ha2 : a 2 = -3 := by
    rw [han 1 (by norm_num), ha1]
    norm_num

  have ha3 : a 3 = -1 / 2 := by
    rw [han 2 (by norm_num), ha2]
    norm_num

  have ha4 : a 4 = 1 / 3 := by
    rw [han 3 (by norm_num), ha3]
    norm_num

  have h2 : ∀ k, a (4 * k + 4) = 1 / 3 := by
    intro k
    induction k with
    | zero =>
      norm_num [ha4]
    | succ k ih =>
      have h1' : a (4 * k + 5) = 2 := by
        rw [show 4 * k + 5 = (4 * k + 4) + 1 by omega]
        rw [han (4 * k + 4) (by omega)]
        rw [ih]
        norm_num
      have h2' : a (4 * k + 6) = -3 := by
        rw [show 4 * k + 6 = (4 * k + 5) + 1 by omega]
        rw [han (4 * k + 5) (by omega)]
        rw [h1']
        norm_num
      have h3' : a (4 * k + 7) = -1 / 2 := by
        rw [show 4 * k + 7 = (4 * k + 6) + 1 by omega]
        rw [han (4 * k + 6) (by omega)]
        rw [h2']
        norm_num
      have h4' : a (4 * k + 8) = 1 / 3 := by
        rw [show 4 * k + 8 = (4 * k + 7) + 1 by omega]
        rw [han (4 * k + 7) (by omega)]
        rw [h3']
        norm_num
      rw [show 4 * (k + 1) + 4 = 4 * k + 8 by omega]
      rw [h4']

  have h3 : a 2008 = 1 / 3 := by
    specialize h2 501
    norm_num at h2 ⊢
    linarith

  rw [h3]
  norm_num