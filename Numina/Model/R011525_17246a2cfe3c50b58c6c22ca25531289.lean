import Mathlib

theorem number_theory_253246 (x : ℕ → ℕ) (h1 : x 1 = 2) (h2 : x 2 = 7)
    (h : ∀ n ≥ 1, x (n + 2) = (x n * x (n + 1)) % 10) :
    x 1998 = 6 := by
  have h3 : x 3 = 4 := by 
    specialize h 1 (by norm_num)
    simp [h1, h2] at h ⊢
    all_goals omega
  have h4 : x 4 = 8 := by 
    specialize h 2 (by norm_num)
    simp [h2, h3] at h ⊢
    all_goals omega
  have h5 : x 5 = 2 := by 
    specialize h 3 (by norm_num)
    simp [h3, h4] at h ⊢
    all_goals omega
  have h6 : x 6 = 6 := by 
    specialize h 4 (by norm_num)
    simp [h4, h5] at h ⊢
    all_goals omega
  have h7 : x 7 = 2 := by 
    specialize h 5 (by norm_num)
    simp [h5, h6] at h ⊢
    all_goals omega
  have h8 : x 8 = 2 := by 
    specialize h 6 (by norm_num)
    simp [h6, h7] at h ⊢
    all_goals omega
  have h9 : x 9 = 4 := by 
    specialize h 7 (by norm_num)
    simp [h7, h8] at h ⊢
    all_goals omega
  have h10 : x 10 = 8 := by 
    specialize h 8 (by norm_num)
    simp [h8, h9] at h ⊢
    all_goals omega
  have h9' : ∀ n : ℕ, x (6 * n + 4) = 8 ∧ x (6 * n + 5) = 2 ∧ x (6 * n + 6) = 6 ∧ 
    x (6 * n + 7) = 2 ∧ x (6 * n + 8) = 2 ∧ x (6 * n + 9) = 4 := by
    intro n
    induction n with
    | zero =>
      constructor 
      · -- Show x (6 * 0 + 4) = 8
        norm_num at *
        exact h4
      constructor
      · -- Show x (6 * 0 + 5) = 2
        norm_num at *
        exact h5
      constructor 
      · -- Show x (6 * 0 + 6) = 6
        norm_num at *
        exact h6
      constructor 
      · -- Show x (6 * 0 + 7) = 2
        norm_num at *
        exact h7
      constructor 
      · -- Show x (6 * 0 + 8) = 2
        norm_num at *
        exact h8
      · -- Show x (6 * 0 + 9) = 4
        norm_num at *
        exact h9
    | succ n ih =>
      have eq1 : x (6 * (n + 1) + 4) = 8 := by
        have eq2 : x (6 * (n + 1) + 4) = (x (6 * n + 8) * x (6 * n + 9)) % 10 := by 
          specialize h (6 * n + 8) (by omega)
          simpa using h
        have hx8 : x (6 * n + 8) = 2 := by
          have eq1 := ih
          norm_num at eq1 ⊢
          omega
        have hx9 : x (6 * n + 9) = 4 := by
          have eq1 := ih
          norm_num at eq1 ⊢
          omega
        rw [eq2] 
        simp [hx8, hx9]
      have eq2 : x (6 * (n + 1) + 5) = 2 := by 
        have eq3 : x (6 * (n + 1) + 5) = (x (6 * n + 9) * x (6 * (n + 1) + 4)) % 10 := by 
          specialize h (6 * n + 9) (by omega)
          simpa using h
        have hx9 : x (6 * n + 9) = 4 := by
          have eq1 := ih
          norm_num at eq1 ⊢
          omega
        rw [eq3] 
        simp [hx9, eq1]
      have eq3 : x (6 * (n + 1) + 6) = 6 := by 
        have eq4 : x (6 * (n + 1) + 6) = (x (6 * (n + 1) + 4) * x (6 * (n + 1) + 5)) % 10 := by 
          specialize h (6 * (n + 1) + 4) (by omega)
          simpa using h 
        rw [eq4] 
        simp [eq1, eq2] 
      have eq4 : x (6 * (n + 1) + 7) = 2 := by 
        have eq5 : x (6 * (n + 1) + 7) = (x (6 * (n + 1) + 5) * x (6 * (n + 1) + 6)) % 10 := by 
          specialize h (6 * (n + 1) + 5) (by omega)
          simpa using h 
        rw [eq5] 
        simp [eq2, eq3] 
      have eq5 : x (6 * (n + 1) + 8) = 2 := by 
        have eq6 : x (6 * (n + 1) + 8) = (x (6 * (n + 1) + 6) * x (6 * (n + 1) + 7)) % 10 := by 
          specialize h (6 * (n + 1) + 6) (by omega)
          simpa using h 
        rw [eq6] 
        simp [eq3, eq4] 
      have eq6 : x (6 * (n + 1) + 9) = 4 := by 
        have eq7 : x (6 * (n + 1) + 9) = (x (6 * (n + 1) + 7) * x (6 * (n + 1) + 8)) % 10 := by 
          specialize h (6 * (n + 1) + 7) (by omega)
          simpa using h 
        rw [eq7] 
        simp [eq4, eq5] 
      exact ⟨eq1, eq2, eq3, eq4, eq5, eq6⟩
  have h1998 : x 1998 = 6 := by
    have eq3 : x (6 * 332 + 6) = 6 := by
      have eq4 : x (6 * 332 + 4) = 8 ∧ x (6 * 332 + 5) = 2 ∧ x (6 * 332 + 6) = 6 ∧ 
          x (6 * 332 + 7) = 2 ∧ x (6 * 332 + 8) = 2 ∧ x (6 * 332 + 9) = 4 := by 
        apply h9'
      tauto
    have eq4 : 6 * 332 + 6 = 1998 := by 
      omega 
    rw [eq4] at eq3 
    tauto 
  exact h1998