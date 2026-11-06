import Mathlib


-- add a term a 0 to simplify the proof
theorem algebra_256869 (a : ℕ → ℤ) (ha0 : a 0 = 21) (ha1 : a 1 = 2) (ha2 : a 2 = -19)
    (han : ∀ n > 0, a (n + 2) = |a (n + 1)| - a n) :
    a 2019 = 17 := by
  have ha3 : a 3 = 17 := by
    specialize han 1 (by omega)
    rw [show 1 + 2 = 3 by omega, ha2, ha1] at han
    norm_num [abs_of_nonneg, abs_of_nonpos] at han ⊢
    exact han

  have ha4 : a 4 = 36 := by
    specialize han 2 (by omega)
    rw [show 2 + 2 = 4 by omega, ha3, ha2] at han
    norm_num [abs_of_nonneg, abs_of_nonpos] at han ⊢
    exact han

  have ha5 : a 5 = 19 := by
    specialize han 3 (by omega)
    rw [show 3 + 2 = 5 by omega, ha4, ha3] at han
    norm_num [abs_of_nonneg, abs_of_nonpos] at han ⊢
    exact han

  have ha6 : a 6 = -17 := by
    specialize han 4 (by omega)
    rw [show 4 + 2 = 6 by omega, ha5, ha4] at han
    norm_num [abs_of_nonneg, abs_of_nonpos] at han ⊢
    exact han

  have ha7 : a 7 = -2 := by
    specialize han 5 (by omega)
    rw [show 5 + 2 = 7 by omega, ha6, ha5] at han
    norm_num [abs_of_nonneg, abs_of_nonpos] at han ⊢
    exact han

  have ha8 : a 8 = 19 := by
    specialize han 6 (by omega)
    rw [show 6 + 2 = 8 by omega, ha7, ha6] at han
    norm_num [abs_of_nonneg, abs_of_nonpos] at han ⊢
    exact han

  have ha9 : a 9 = 21 := by
    specialize han 7 (by omega)
    rw [show 7 + 2 = 9 by omega, ha8, ha7] at han
    norm_num [abs_of_nonneg, abs_of_nonpos] at han ⊢
    exact han

  have ha10 : a 10 = 2 := by
    specialize han 8 (by omega)
    rw [show 8 + 2 = 10 by omega, ha9, ha8] at han
    norm_num [abs_of_nonneg, abs_of_nonpos] at han ⊢
    exact han
  
  have aneq : ∀ (k : ℕ), (a (9 * k) = 21 ∧ a (9 * k + 1) = 2 ∧ 
    a (9 * k + 2) = -19 ∧ a (9 * k + 3) = 17 ∧ a (9 * k + 4) = 36 ∧ a (9 * k + 5) = 19 ∧ a (9 * k + 6) = -17 ∧ a (9 * k + 7) = - 2 ∧ a (9 * k + 8) = 19) := by 
    intro k
    induction k with 
    | zero => simp_all
    | succ m ih => 
      obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩ := ih
      have h1' : a (9 * (m + 1)) = 21 := by 
        calc 
          _ = a (9 * m + 7 + 2) := by ring_nf
          _ = 21 := by 
            rw [han]
            rw [h8, h7]
            norm_num
            linarith
      have h2' : a (9 * (m + 1) + 1) = 2 := by
        calc
          _ = a (9 * m + 7 + 2 + 1) := by ring_nf
          _ = 2 := by
            rw [han]
            rw [h8]
            have aux : a (9 * m + 8 + 1) = a (9 * (m + 1)) := by 
              ring_nf
            rw [aux, h1']
            norm_num
            linarith
      have h3' : a (9 * (m + 1) + 2) = -19 := by
        rw [han, h2', h1']
        norm_num
        linarith
      have h4' : a (9 * (m + 1) + 3) = 17 := by
        rw [han, h3', h2']
        norm_num
        linarith
      have h5' : a (9 * (m + 1) + 4) = 36 := by
        rw [han, h4', h3']
        norm_num
        linarith
      have h6' : a (9 * (m + 1) + 5) = 19 := by
        rw [han, h5', h4']
        norm_num
        linarith
      have h7' : a (9 * (m + 1) + 6) = -17 := by
        rw [han, h6', h5']
        norm_num
        linarith
      have h8' : a (9 * (m + 1) + 7) = -2 := by
        rw [han, h7', h6']
        norm_num
        linarith
      have h0' : a (9 * (m + 1) + 8) = 19 := by
        rw [han, h8', h7']
        norm_num
        linarith
      exact ⟨h1', h2', h3', h4', h5', h6', h7', h8', h0' ⟩
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩ := aneq 224
  norm_num at h3
  exact h3