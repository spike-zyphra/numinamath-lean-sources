import Mathlib

theorem algebra_291370 {a : ℕ → ℝ} (ha1 : a 1 = 5)
    (han : ∀ n ≥ 2, a n = (2 * a (n - 1) - 1) / (a (n - 1) - 2)) :
    ∑ i in Finset.Icc 1 100, a i = 400 := by
  have ha2 : a 2 = 3 := by 
    specialize han 2 (by norm_num)
    rw [show a 1 = (5 : ℝ) by linarith [ha1]] at han
    norm_num at han ⊢
    linarith

  have h1 : ∀ (n : ℕ), a (2 * n + 1) = 5 := by 
    intro n
    induction n with
    | zero => 
      norm_num 
      all_goals linarith [ha1]
    | succ n ih =>
      have eq1 : 2 * (n + 1) + 1 = (2 * n + 2 + 1 : ℕ) := by ring
      rw [eq1]
      have ha3 : a (2 * n + 3) = 5 := by
        have ha2n2 : a (2 * n + 2) = 3 := by 
          have eq2 : a (2 * n + 2) = (2 * a (2 * n + 1) - 1) / (a (2 * n + 1) - 2) := by 
            specialize han (2 * n + 2) (by omega)
            simpa using han
          rw [show a (2 * n + 1) = (5 : ℝ) by linarith [ih]] at eq2
          norm_num at eq2 ⊢ 
          linarith 
        have eq3 : a (2 * n + 3) = (2 * a (2 * n + 2) - 1) / (a (2 * n + 2) - 2) := by 
          specialize han (2 * n + 3) (by omega)
          simpa using han 
        rw [show a (2 * n + 2) = (3 : ℝ) by linarith [ha2n2]] at eq3 
        norm_num at eq3 ⊢ 
        linarith 
      simpa using ha3

  have h2 : ∀ (n : ℕ), a (2 * n + 2) = 3 := by 
    intro n 
    have eq1 : a (2 * n + 2) = (2 * a (2 * n + 1) - 1) / (a (2 * n + 1) - 2) := by 
      specialize han (2 * n + 2) (by omega)
      simpa using han 
    have ha1' : a (2 * n + 1) = (5 : ℝ) := by 
      specialize h1 n 
      simpa using h1 
    rw [ha1'] at eq1 
    norm_num at eq1 ⊢ 
    linarith 

  norm_num [Finset.sum_Icc_succ_top, ha1, ha2, han, h1, h2]
  <;> norm_num