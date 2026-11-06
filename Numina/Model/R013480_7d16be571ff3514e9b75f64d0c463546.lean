import Mathlib

open Finset

theorem algebra_96420 {a : ℕ → ℝ} (ha1 : a 1 = 2) (ha2 : a 2 = 3)
    (han : ∀ n ≥ 3, a n = a (n - 1) / a (n - 2)) :
    a 2006 = 3 := by

  have h2 : ∀ (k : ℕ), a (6 * k + 1) = 2 ∧ a (6 * k + 2) = 3 := by
    intro k
    induction k with
    | zero =>
      constructor
      · exact ha1
      · exact ha2
    | succ k ih =>
      have ha3 : a (6 * k + 3) = a (6 * k + 2) / a (6 * k + 1) := by
        specialize han (6 * k + 3) (by omega)
        simpa using han
      have ha3' : a (6 * k + 3) = 3 / 2 := by
        rw [ha3]
        rw [ih.2, ih.1]
        all_goals norm_num
      have ha4 : a (6 * k + 4) = a (6 * k + 3) / a (6 * k + 2) := by
        specialize han (6 * k + 4) ( by omega)
        simpa using han
      have ha4' : a (6 * k + 4) = 1 / 2 := by
        rw [ha4, ha3']
        rw [ih.2]
        all_goals norm_num
      -- Compute a_5
      have ha5 : a (6 * k + 5) = a (6 * k + 4) / a (6 * k + 3) := by
        specialize han (6 * k + 5) (by omega)
        simpa using han
      have ha5' : a (6 * k + 5) = 1 / 3 := by
        rw [ha5, ha4']
        rw [ha3']
        all_goals norm_num
      have ha6 : a (6 * k + 6) = a (6 * k + 5) / a (6 * k + 4) := by
        specialize han (6 * k + 6) (by omega)
        simpa using han
      have ha6' : a (6 * k + 6) = 2 / 3 := by
        rw [ha6, ha5']
        rw [ha4']
        all_goals norm_num
      -- Compute a_7 and a_8
      have ha7 : a (6 * k + 7) = a (6 * k + 6) / a (6 * k + 5) := by
        specialize han (6 * k + 7) (by omega)
        simpa using han
      have ha7' : a (6 * k + 7) = 2 := by
        rw [ha7, ha6']
        rw [ha5']
        all_goals norm_num
      -- Compute a_8
      have ha8 : a (6 * k + 8) = a (6 * k + 7) / a (6 * k + 6) := by
        specialize han (6 * k + 8) (by omega)
        simpa using han
      have ha8' : a (6 * k + 8) = 3 := by
        rw [ha8, ha7']
        rw [ha6']
        all_goals norm_num
      constructor
      · -- Show that a (6 * (k + 1) + 1) = 2
        have eq1 : 6 * (k + 1) + 1 = 6 * k + 7 := by
          omega
        rw [eq1]
        exact ha7'
      · -- Show that a (6 * (k + 1) + 2) = 3
        have eq2 : 6 * (k + 1) + 2 = 6 * k + 8 := by
          omega
        rw [eq2]
        exact ha8'

  have h3 := (h2 334).2
  norm_num at h3 ⊢
  exact h3