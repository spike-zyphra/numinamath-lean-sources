import Mathlib

open Finset

theorem algebra_295180 {a : ℕ → ℝ}
    (ha1 : a 1 = 2) (ha2 : a 2 = 3)
    (han : ∀ n ≥ 3, a n = a (n - 1) / a (n - 2)) :
    a 2014 = 1 / 2 := by 
  have ha3 : a 3 = a 2 / a 1 := han 3 (by norm_num)
  rw [ha2, ha1] at ha3
  have ha4 : a 4 = a 3 / a 2 := han 4 (by norm_num)
  rw [ha3, ha2] at ha4
  have ha4_val : a 4 = 1 / 2 := by
    norm_num at ha4 ⊢
    linarith 
  have ha5 : a 5 = a 4 / a 3 := han 5 (by norm_num)
  rw [ha4_val, ha3] at ha5
  have ha5_val : a 5 = 1 / 3 := by
    norm_num at ha5 ⊢
    linarith
  have ha6 : a 6 = a 5 / a 4 := han 6 (by norm_num)
  rw [ha5_val, ha4_val] at ha6
  have ha6_val : a 6 = 2 / 3 := by
    norm_num at ha6 ⊢
    linarith 
  have h1 : ∀ n : ℕ, a (6 * n + 1) = 2 ∧ a (6 * n + 2) = 3 ∧ a (6 * n + 3) = 3 / 2 ∧ a (6 * n + 4) = 1 / 2 ∧ a (6 * n + 5) = 1 / 3 ∧ a (6 * n + 6) = 2 / 3 := by
    intro n 
    induction n with 
    | zero =>
      simp [show (6 * 0 + 1 : ℕ) = 1 by omega, 
          show (6 * 0 + 2 : ℕ) = 2 by omega, 
          show (6 * 0 + 3 : ℕ) = 3 by omega, 
          show (6 * 0 + 4 : ℕ) = 4 by omega, 
          show (6 * 0 + 5 : ℕ) = 5 by omega, 
          show (6 * 0 + 6 : ℕ) = 6 by omega, 
          ha1, ha2, ha3, ha4_val, ha5_val, ha6_val]
    | succ n ih =>
      have ha7 : a (6 * n + 7) = a (6 * n + 6) / a (6 * n + 5) := by 
        specialize han (6 * n + 7) (by linarith)
        simpa using han 
      have ha8 : a (6 * n + 8) = a (6 * n + 7) / a (6 * n + 6) := by 
        specialize han (6 * n + 8) (by linarith)
        simpa using han 
      have ha9 : a (6 * n + 9) = a (6 * n + 8) / a (6 * n + 7) := by 
        specialize han (6 * n + 9) (by linarith)
        simpa using han 
      have ha10 : a (6 * n + 10) = a (6 * n + 9) / a (6 * n + 8) := by 
        specialize han (6 * n + 10) (by linarith)
        simpa using han 
      have ha11 : a (6 * n + 11) = a (6 * n + 10) / a (6 * n + 9) := by 
        specialize han (6 * n + 11) (by linarith)
        simpa using han 
      have ha12 : a (6 * n + 12) = a (6 * n + 11) / a (6 * n + 10) := by 
        specialize han (6 * n + 12) (by linarith)
        simpa using han 
      simp [show (6 * (n + 1) + 1 : ℕ) = (6 * n + 7 : ℕ) by omega, 
          show (6 * (n + 1) + 2 : ℕ) = (6 * n + 8 : ℕ) by omega, 
          show (6 * (n + 1) + 3 : ℕ) = (6 * n + 9 : ℕ) by omega, 
          show (6 * (n + 1) + 4 : ℕ) = (6 * n + 10 : ℕ) by omega, 
          show (6 * (n + 1) + 5 : ℕ) = (6 * n + 11 : ℕ) by omega, 
          show (6 * (n + 1) + 6 : ℕ) = (6 * n + 12 : ℕ) by omega] 
      <;> 
        norm_num [ha7, ha8, ha9, ha10, ha11, ha12] at *
      <;> 
        norm_num [ih] at *
      <;> 
        try { linarith }
  have h4 : (2014 : ℕ) = 6 * 335 + 4 := by omega 
  have h5 : a 2014 = 1 / 2 := by 
    rw [h4] 
    have eq1 := (h1 335).2.2.2.1 
    norm_num at eq1 ⊢ 
    linarith 
  exact h5