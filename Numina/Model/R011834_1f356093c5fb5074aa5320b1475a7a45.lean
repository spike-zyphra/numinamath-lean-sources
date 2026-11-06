import Mathlib

theorem algebra_321316 (a : ℕ → ℤ) (ha1 : a 1 = 2) (ha2 : a 2 = 10) (hn : ∀ n > 0, a (n + 2) = a (n + 1) - a n) : a 2015 = - 10 := by
  have ha3 : a 3 = a 2 - a 1 := hn 1 (by norm_num)
  rw [ha2, ha1] at ha3
  norm_num at ha3
  have ha4 : a 4 = a 3 - a 2 := hn 2 (by norm_num)
  rw [ha3, ha2] at ha4
  norm_num at ha4
  have ha5 : a 5 = a 4 - a 3 := hn 3 (by norm_num)
  rw [ha4, ha3] at ha5
  norm_num at ha5
  have ha6 : a 6 = a 5 - a 4 := hn 4 (by norm_num)
  rw [ha5, ha4] at ha6
  norm_num at ha6

  have h1 : ∀ (k : ℕ), a (6 * k + 1) = 2 ∧ a (6 * k + 2) = 10 ∧ a (6 * k + 3) = 8 ∧ a (6 * k + 4) = -2 ∧ a (6 * k + 5) = -10 ∧ a (6 * k + 6) = -8 := by
    intro k
    induction k with
    | zero =>
      constructor
      · exact ha1
      constructor
      · exact ha2
      constructor
      · exact ha3
      constructor
      · exact ha4
      constructor
      · exact ha5
      · exact ha6
    | succ k ih =>
      rcases ih with ⟨ha1', ha2', ha3', ha4', ha5', ha6'⟩
      have ha7 : a (6 * k + 7) = a (6 * k + 6) - a (6 * k + 5) := hn (6 * k + 5) (by omega)
      have ha8 : a (6 * k + 8) = a (6 * k + 7) - a (6 * k + 6) := hn (6 * k + 6) (by omega)
      have ha9 : a (6 * k + 9) = a (6 * k + 8) - a (6 * k + 7) := hn (6 * k + 7) (by omega)
      have ha10 : a (6 * k + 10) = a (6 * k + 9) - a (6 * k + 8) := hn (6 * k + 8) (by omega)
      have ha11 : a (6 * k + 11) = a (6 * k + 10) - a (6 * k + 9) := hn (6 * k + 9) (by omega)
      have ha12 : a (6 * k + 12) = a (6 * k + 11) - a (6 * k + 10) := hn (6 * k + 10) (by omega)
      constructor
      · -- Prove $a (6 * (k + 1) + 1) = 2$
        rw [show 6 * (k + 1) + 1 = 6 * k + 7 by omega]
        have ha7_eq : a (6 * k + 7) = 2 := by
          rw [ha7]
          omega
        exact ha7_eq
      constructor
      · -- Prove $a (6 * (k + 1) + 2) = 10$
        rw [show 6 * (k + 1) + 2 = 6 * k + 8 by omega]
        have ha8_eq : a (6 * k + 8) = 10 := by
          rw [ha8]
          omega
        exact ha8_eq
      constructor
      · -- Prove $a (6 * (k + 1) + 3) = 8$
        rw [show 6 * (k + 1) + 3 = 6 * k + 9 by omega]
        have ha9_eq : a (6 * k + 9) = 8 := by
          rw [ha9]
          omega
        exact ha9_eq
      constructor
      · -- Prove $a (6 * (k + 1) + 4) = -2$
        rw [show 6 * (k + 1) + 4 = 6 * k + 10 by omega]
        have ha10_eq : a (6 * k + 10) = -2 := by
          rw [ha10]
          omega
        exact ha10_eq
      constructor
      · -- Prove $a (6 * (k + 1) + 5) = -10$
        rw [show 6 * (k + 1) + 5 = 6 * k + 11 by omega]
        have ha11_eq : a (6 * k + 11) = -10 := by
          rw [ha11]
          omega
        exact ha11_eq
      · -- Prove $a (6 * (k + 1) + 6) = -8$
        rw [show 6 * (k + 1) + 6 = 6 * k + 12 by omega]
        have ha12_eq : a (6 * k + 12) = -8 := by
          rw [ha12]
          omega
        exact ha12_eq

  have h2015 : 2015 = 6 * 335 + 5 := by norm_num
  have ha2015 : a 2015 = -10 := by
    rw [h2015]
    have h2 : a (6 * 335 + 1) = 2 ∧ a (6 * 335 + 2) = 10 ∧ a (6 * 335 + 3) = 8 ∧ a (6 * 335 + 4) = -2 ∧ a (6 * 335 + 5) = -10 ∧ a (6 * 335 + 6) = -8 := h1 335
    tauto
  exact ha2015