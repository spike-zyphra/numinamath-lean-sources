import Mathlib

theorem algebra_156406 {f : ℕ → ℕ} (hf : f 2 = 1 ∧ f 5 = 2 ∧ f 3 = 3 ∧ f 1 = 4 ∧ f 4 = 5)
    (a : ℕ → ℕ) (ha : a 0 = 5) (h : ∀ n, a (n + 1) = f (a n)) :
    a 2007 = 4 := by
  rcases hf with ⟨h2, h5, h3, h1, h4⟩
  have ha1 : a 1 = 2 := by 
    specialize h 0
    rw [ha] at h
    have : a 1 = f 5 := by 
      simpa using h
    rw [this]
    all_goals 
      omega
  have ha2 : a 2 = 1 := by 
    specialize h 1
    rw [ha1] at h
    have : a 2 = f 2 := by 
      simpa using h
    rw [this]
    all_goals 
      omega
  have ha3 : a 3 = 4 := by 
    specialize h 2
    rw [ha2] at h
    have : a 3 = f 1 := by 
      simpa using h
    rw [this]
    all_goals 
      omega
  have ha4 : a 4 = 5 := by 
    specialize h 3
    rw [ha3] at h
    have : a 4 = f 4 := by 
      simpa using h
    rw [this]
    all_goals 
      omega
  have h_cycle : ∀ k, a (4 * k + 3) = 4 := by 
    intro k 
    induction k with 
    | zero => 
      simp [ha3]
    | succ k ih =>
      have eq1 : a (4 * (k + 1) + 3) = 4 := by
        have eq2 : 4 * (k + 1) + 3 = 4 * k + 7 := by 
          omega 
        rw [eq2]
        have eq3 : a (4 * k + 7) = f (a (4 * k + 6)) := by 
          specialize h (4 * k + 6)
          simpa using h 
        have eq4 : a (4 * k + 6) = f (a (4 * k + 5)) := by 
          specialize h (4 * k + 5)
          simpa using h 
        have eq5 : a (4 * k + 5) = f (a (4 * k + 4)) := by 
          specialize h (4 * k + 4)
          simpa using h 
        have eq6 : a (4 * k + 4) = f (a (4 * k + 3)) := by 
          specialize h (4 * k + 3)
          simpa using h 
        rw [eq3, eq4, eq5, eq6]
        simp [ih, h1, h2, h4, h5]
      exact eq1 
  have h2k : ∃ k, 2007 = 4 * k + 3 := by 
    use 501
    all_goals 
      norm_num 
  rcases h2k with ⟨k, hk⟩ 
  have h2007 : a 2007 = 4 := by 
    rw [show 2007 = 4 * k + 3 by linarith [hk]]
    exact h_cycle k 
  exact h2007