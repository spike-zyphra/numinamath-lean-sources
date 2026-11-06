import Mathlib

open scoped BigOperators

theorem algebra_255197 {t : ℕ → ℝ}
  (ht1 : t 1 = 2)
  (hxn : ∀ n > 0, t (n + 1) = (t n - 1) / (t n + 1)) :
  t 2011 = -1 / 2 := by

  have ht2 : t 2 = 1 / 3 := by
    rw [hxn 1 (by norm_num), ht1]
    norm_num

  have ht3 : t 3 = -1 / 2 := by
    rw [hxn 2 (by norm_num), ht2]
    norm_num

  have ht4 : t 4 = -3 := by
    rw [hxn 3 (by norm_num), ht3]
    norm_num

  have ht5 : t 5 = 2 := by
    rw [hxn 4 (by norm_num), ht4]
    norm_num

  have h : ∀ k, t (4 * k + 3) = -1 / 2 := by
    intro k
    induction k with
    | zero =>
      norm_num [ht3]
    | succ k ih =>
      have ht4k4 : t (4 * k + 4) = -3 := by
        rw [show 4 * k + 4 = (4 * k + 3) + 1 by omega]
        rw [hxn (4 * k + 3) (by omega)]
        rw [ih]
        norm_num
      have ht4k5 : t (4 * k + 5) = 2 := by
        rw [show 4 * k + 5 = (4 * k + 4) + 1 by omega]
        rw [hxn (4 * k + 4) (by omega)]
        rw [ht4k4]
        norm_num
      have ht4k6 : t (4 * k + 6) = 1 / 3 := by
        rw [show 4 * k + 6 = (4 * k + 5) + 1 by omega]
        rw [hxn (4 * k + 5) (by omega)]
        rw [ht4k5]
        norm_num
      have ht4k7 : t (4 * k + 7) = -1 / 2 := by
        rw [show 4 * k + 7 = (4 * k + 6) + 1 by omega]
        rw [hxn (4 * k + 6) (by omega)]
        rw [ht4k6]
        norm_num
      have eq : 4 * (k + 1) + 3 = 4 * k + 7 := by
        omega
      rw [eq]
      exact ht4k7

  have eq2 : 4 * 502 + 3 = 2011 := by
    norm_num
  specialize h 502
  rw [eq2] at h
  linarith