import Mathlib

theorem number_theory_237465 (a : ℕ → ℕ) (ha : a 0 = 6)
    (h : ∀ n, Even (a n) → a (n + 1) = a n / 2)
    (h' : ∀ n, Odd (a n) → a (n + 1) = 3 * a n + 1) :
    a 2017 = 2 := by
  have ha1 : a 1 = 3 := by
    have h0 : Even (a 0) := by
      rw [ha]
      decide
    have h1 : a 1 = a 0 / 2 := h 0 h0
    simp [ha] at h1 ⊢
    omega
  have ha2 : a 2 = 10 := by
    have h1 : Odd (a 1) := by
      rw [ha1]
      decide
    have h2 : a 2 = 3 * a 1 + 1 := h' 1 h1
    simp [ha1] at h2 ⊢
    omega
  have ha3 : a 3 = 5 := by 
    have h2 : Even (a 2) := by
      rw [ha2]
      decide
    have h3 : a 3 = a 2 / 2 := h 2 h2
    simp [ha2] at h3 ⊢
    omega
  have ha4 : a 4 = 16 := by 
    have h3 : Odd (a 3) := by 
      rw [ha3]
      decide
    have h4 : a 4 = 3 * a 3 + 1 := h' 3 h3
    simp [ha3] at h4 ⊢
    omega
  have ha5 : a 5 = 8 := by
    have h4 : Even (a 4) := by
      rw [ha4]
      decide
    have h5 : a 5 = a 4 / 2 := h 4 h4
    simp [ha4] at h5 ⊢
    omega
  have ha6 : a 6 = 4 := by 
    have h5 : Even (a 5) := by
      rw [ha5]
      decide
    have h6 : a 6 = a 5 / 2 := h 5 h5
    simp [ha5] at h6 ⊢
    omega
  have ha7 : a 7 = 2 := by
    have h6 : Even (a 6) := by
      rw [ha6]
      decide
    have h7 : a 7 = a 6 / 2 := h 6 h6
    simp [ha6] at h7 ⊢
    omega
  have h11 : ∀ (n : ℕ), a (3 * n + 7) = 2 := by
    intro n
    induction n with
    | zero =>
      norm_num
      all_goals
      exact ha7
    | succ n ih =>
      have h1 : a (3 * n + 7) = 2 := ih
      have ha1 : a (3 * n + 8) = 1 := by
        have h10 : Even (a (3 * n + 7)) := by
          rw [h1]
          decide
        have h11 : a (3 * n + 7 + 1) = a (3 * n + 7) / 2 := h (3 * n + 7) h10
        have h12 : a (3 * n + 7 + 1) = 1 := by
          simp [h1] at h11 ⊢
          omega
        have h13 : 3 * n + 7 + 1 = 3 * n + 8 := by omega
        rw [h13] at h12
        exact h12
      have ha2 : a (3 * n + 9) = 4 := by
        have h10 : Odd (a (3 * n + 8)) := by
          rw [ha1]
          decide
        have h11 : a (3 * n + 8 + 1) = 3 * a (3 * n + 8) + 1 := h' (3 * n + 8) h10
        have h12 : a (3 * n + 8 + 1) = 4 := by
          simp [ha1] at h11 ⊢
          omega
        have h13 : 3 * n + 8 + 1 = 3 * n + 9 := by omega
        rw [h13] at h12
        exact h12
      have ha3 : a (3 * (n + 1) + 7) = 2 := by
        have ha100 : a (3 * n + 10) = 2 := by
          have ha105 : a (3 * n + 9) = 4 := ha2
          have h10 : Even (a (3 * n + 9)) := by
            rw [ha2]
            decide
          have h11 : a (3 * n + 9 + 1) = a (3 * n + 9) / 2 := h (3 * n + 9) h10
          have h12 : a (3 * n + 10) = 2 := by
            have h14 : 3 * n + 9 + 1 = 3 * n + 10 := by omega
            rw [h14] at h11
            simp [ha2] at h11 ⊢
            omega
          exact h12
        have h14 : 3 * (n + 1) + 7 = 3 * n + 10 := by omega
        rw [h14] 
        exact ha100
      exact ha3
  have eq1 : 2017 = 3 * 670 + 7 := by omega
  rw [eq1]
  apply h11 670