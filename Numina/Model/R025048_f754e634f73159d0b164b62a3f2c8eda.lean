import Mathlib

theorem algebra_114199 (a : ℕ → ℝ) (ha1 : a 1 = 2) (han : ∀ n, a (n + 1) = -1 / (a n + 1)) :
    a 2001 = -3 / 2 := by

  have ha2 : a 2 = -1 / 3 := by
    rw [han 1, ha1]
    norm_num
  have ha3 : a 3 = -3 / 2 := by
    rw [han 2, ha2]
    norm_num
  have ha4 : a 4 = 2 := by
    rw [han 3, ha3]
    norm_num
  have h : ∀ k : ℕ, a (3 * k + 1) = 2 ∧ a (3 * k + 2) = -1 / 3 ∧ a (3 * k + 3) = -3 / 2 := by
    intro k
    induction k with
    | zero =>
      constructor
      · simpa using ha1
      constructor
      · simpa using ha2
      · simpa using ha3
    | succ k ih =>
      have ha1' : a (3 * (k + 1) + 1) = 2 := by
        have eq1 : 3 * (k + 1) + 1 = 3 * k + 4 := by omega
        rw [eq1]
        have eq2 : a (3 * k + 4) = -1 / (a (3 * k + 3) + 1) := by
          specialize han (3 * k + 3)
          simpa using han
        rw [eq2]
        have eq3 : a (3 * k + 3) = -3 / 2 := (ih.2.2)
        rw [eq3]
        norm_num
      have ha2' : a (3 * (k + 1) + 2) = -1 / 3 := by
        have eq1 : 3 * (k + 1) + 2 = 3 * k + 5 := by omega
        rw [eq1]
        have eq2 : a (3 * k + 5) = -1 / (a (3 * k + 4) + 1) := by
          specialize han (3 * k + 4)
          simpa using han
        rw [eq2]
        have eq3 : a (3 * k + 4) = 2 := by
          have eq1 : 3 * (k + 1) + 1 = 3 * k + 4 := by omega
          rw [eq1] at ha1'
          linarith
        rw [eq3]
        norm_num
      have ha3' : a (3 * (k + 1) + 3) = -3 / 2 := by
        have eq1 : 3 * (k + 1) + 3 = 3 * k + 6 := by omega
        rw [eq1]
        have eq2 : a (3 * k + 6) = -1 / (a (3 * k + 5) + 1) := by
          specialize han (3 * k + 5)
          simpa using han
        rw [eq2]
        have eq3 : a (3 * k + 5) = -1 / 3 := by
          have eq1 : 3 * (k + 1) + 2 = 3 * k + 5 := by omega
          rw [eq1] at ha2'
          linarith
        rw [eq3]
        norm_num
      constructor
      · exact ha1'
      constructor
      · exact ha2'
      · exact ha3'
  have eq := (h 666).2.2
  norm_num at eq ⊢
  all_goals linarith