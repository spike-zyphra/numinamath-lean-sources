import Mathlib

theorem algebra_316780 (a : ℕ → ℝ) (ha : a 1 = 1) (ha' : a 2 = 1)
    (ha'' : a 3 = 2) (h : ∀ n ≥ 1, a n * a (n + 1) * a (n + 2) * a (n + 3) = a n + a (n + 1) + a (n + 2) + a (n + 3))
    (h' : ∀ n > 0, a n * a (n + 1) * a (n + 2) ≠ 1) :
    ∑ k in Finset.Icc 1 100, a k = 200 := by

  have ha4 : a 4 = 4 := by 
    have eq1 := h 1 (by norm_num)
    simp [ha, ha', ha''] at eq1 
    linarith

  have ha5 : a 5 = 1 := by 
    have eq2 := h 2 (by norm_num)
    norm_num [ha', ha'', ha4] at eq2 
    nlinarith

  have ha6 : a 6 = 1 := by 
    have eq3 := h 3 (by norm_num)
    norm_num [ha4, ha5] at eq3 
    nlinarith

  have ha7 : a 7 = 2 := by 
    have eq4 := h 4 (by norm_num)
    norm_num [ha5, ha6] at eq4 
    nlinarith

  have ha8 : a 8 = 4 := by 
    have eq5 := h 5 (by norm_num)
    norm_num [ha6, ha7] at eq5 
    nlinarith

  have h1 : ∀ (k : ℕ), a (4 * k + 1) = 1 ∧ a (4 * k + 2) = 1 ∧ a (4 * k + 3) = 2 ∧ a (4 * k + 4) = 4 := by 
    intro k 
    induction k with 
    | zero => 
      constructor 
      · -- a 1 = 1 
        exact ha 
      constructor 
      · -- a 2 = 1 
        exact ha' 
      constructor 
      · -- a 3 = 2 
        exact ha'' 
      · -- a 4 = 4 
        exact ha4 
    | succ k ih => 
      rcases ih with ⟨h11, h12, h13, h14⟩ 
      have ha5' : a (4 * k + 5) = 1 := by 
        have eq1 := h (4 * k + 2) (by linarith)
        simp [h12, h13, h14] at eq1 
        ring_nf at eq1 ⊢ 
        linarith 
      have ha6' : a (4 * k + 6) = 1 := by 
        have eq2 := h (4 * k + 3) (by linarith)
        simp [h13, h14, ha5'] at eq2 
        ring_nf at eq2 ⊢ 
        linarith 
      have ha7' : a (4 * k + 7) = 2 := by 
        have eq3 := h (4 * k + 4) (by linarith)
        simp [h14, ha5', ha6'] at eq3 
        ring_nf at eq3 ⊢ 
        linarith 
      have ha8' : a (4 * k + 8) = 4 := by 
        have eq4 := h (4 * k + 5) (by linarith)
        simp [ha5', ha6', ha7'] at eq4 
        ring_nf at eq4 ⊢ 
        linarith 
      constructor 
      · -- Show a (4 * (k + 1) + 1) = 1 
        have eq1 : 4 * (k + 1) + 1 = 4 * k + 5 := by ring 
        rw [eq1] 
        exact ha5' 
      constructor 
      · -- Show a (4 * (k + 1) + 2) = 1 
        have eq2 : 4 * (k + 1) + 2 = 4 * k + 6 := by ring 
        rw [eq2] 
        exact ha6' 
      constructor 
      · -- Show a (4 * (k + 1) + 3) = 2 
        have eq3 : 4 * (k + 1) + 3 = 4 * k + 7 := by ring 
        rw [eq3] 
        exact ha7' 
      · -- Show a (4 * (k + 1) + 4) = 4 
        have eq4 : 4 * (k + 1) + 4 = 4 * k + 8 := by ring 
        rw [eq4] 
        exact ha8' 

  have sum_eq : ∀ m : ℕ, ∑ k in Finset.Icc 1 (4 * m), a k = 8 * (m : ℝ) := by 
    intro m 
    induction m with 
    | zero =>
      simp
    | succ m ih => 
      rw [show 4 * (m + 1 : ℕ) = 4 * (m : ℕ) + 4 by omega]
      rw [Finset.sum_Icc_succ_top (by linarith), Finset.sum_Icc_succ_top (by linarith), 
          Finset.sum_Icc_succ_top (by linarith), Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      have ha1' : a (4 * (m : ℕ) + 1) = 1 := by 
        have h11 := h1 m 
        exact h11.1 
      have ha2' : a (4 * (m : ℕ) + 2) = 1 := by 
        have h11 := h1 m 
        exact h11.2.1 
      have ha3' : a (4 * (m : ℕ) + 3) = 2 := by 
        have h11 := h1 m 
        exact h11.2.2.1 
      have ha4' : a (4 * (m : ℕ) + 4) = 4 := by 
        have h11 := h1 m 
        exact h11.2.2.2 
      simp [ha1', ha2', ha3', ha4']
      all_goals linarith

  have h100 : ∑ k in Finset.Icc 1 100, a k = 200 := by 
    rw [show (100 : ℕ) = 4 * (25 : ℕ) by norm_num]
    specialize sum_eq 25 
    norm_num at sum_eq ⊢ 
    linarith

  exact h100