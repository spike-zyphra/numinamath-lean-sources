import Mathlib

theorem number_theory_275985 (a : ℕ → ℕ)
    (h₀ : a 0 = 6)
    (h₁ : ∀ n, Even (a n) → a (n + 1) = a n / 2)
    (h₂ : ∀ n, Odd (a n) → a (n + 1) = 3 * a n + 1) :
    a 99 = 4 := by
  have h_a1 : a 1 = 3 := by
    have h_even_0 : Even (a 0) := by rw [h₀]; exact ⟨3, rfl⟩
    have h : a 1 = a 0 / 2 := h₁ 0 h_even_0
    rw [h₀] at h
    exact h

  have h_a2 : a 2 = 10 := by
    have h_odd_1 : Odd (a 1) := by rw [h_a1]; exact ⟨1, by norm_num⟩
    have h : a 2 = 3 * a 1 + 1 := h₂ 1 h_odd_1
    rw [h_a1] at h
    exact h

  have h_a3 : a 3 = 5 := by
    have h_even_2 : Even (a 2) := by rw [h_a2]; exact ⟨5, rfl⟩
    have h : a 3 = a 2 / 2 := h₁ 2 h_even_2
    rw [h_a2] at h
    exact h

  have h_a4 : a 4 = 16 := by
    have h_odd_3 : Odd (a 3) := by rw [h_a3]; exact ⟨2, by norm_num⟩
    have h : a 4 = 3 * a 3 + 1 := h₂ 3 h_odd_3
    rw [h_a3] at h
    exact h

  have h_a5 : a 5 = 8 := by
    have h_even_4 : Even (a 4) := by rw [h_a4]; exact ⟨8, rfl⟩
    have h : a 5 = a 4 / 2 := h₁ 4 h_even_4
    rw [h_a4] at h
    exact h

  have h_a6 : a 6 = 4 := by
    have h_even_5 : Even (a 5) := by rw [h_a5]; exact ⟨4, rfl⟩
    have h : a 6 = a 5 / 2 := h₁ 5 h_even_5
    rw [h_a5] at h
    exact h

  have h_a7 : a 7 = 2 := by
    have h_even_6 : Even (a 6) := by rw [h_a6]; exact ⟨2, rfl⟩
    have h : a 7 = a 6 / 2 := h₁ 6 h_even_6
    rw [h_a6] at h
    exact h

  have h_a8 : a 8 = 1 := by
    have h_even_7 : Even (a 7) := by rw [h_a7]; exact ⟨1, rfl⟩
    have h : a 8 = a 7 / 2 := h₁ 7 h_even_7
    rw [h_a7] at h
    exact h

  have h_a9 : a 9 = 4 := by
    have h_odd_8 : Odd (a 8) := by rw [h_a8]; exact ⟨0, by norm_num⟩
    have h : a 9 = 3 * a 8 + 1 := h₂ 8 h_odd_8
    rw [h_a8] at h
    exact h

  have cycle_lemma : ∀ k : ℕ, a (6 + 3 * k) = 4 := by
    intro k
    induction k with 
    | zero =>
      norm_num [h_a6]
    | succ k ih =>
      have h1 : a (6 + 3 * k) = 4 := ih
      have h2 : a (6 + 3 * k + 1) = 2 := by
        have h4 : Even (a (6 + 3 * k)) := by 
          rw [show a (6 + 3 * k) = 4 by omega]
          exact ⟨2, by norm_num⟩
        have h5 : a (6 + 3 * k + 1) = a (6 + 3 * k) / 2 := h₁ (6 + 3 * k) h4
        rw [show a (6 + 3 * k) = 4 by omega] at h5
        omega
      have h3 : a (6 + 3 * k + 2) = 1 := by 
        have h4 : Even (a (6 + 3 * k + 1)) := by
          rw [show a (6 + 3 * k + 1) = 2 by omega]
          exact ⟨1, by norm_num⟩
        have h5 : a (6 + 3 * k + 2) = a (6 + 3 * k + 1) / 2 := h₁ (6 + 3 * k + 1) h4
        rw [show a (6 + 3 * k + 1) = 2 by omega] at h5
        omega
      have h5 : a (6 + 3 * (k + 1)) = 4 := by 
        have h6 : Odd (a (6 + 3 * k + 2)) := by 
          rw [show a (6 + 3 * k + 2) = 1 by omega]
          exact ⟨0, by norm_num⟩
        have h7 : a (6 + 3 * k + 3) = 3 * a (6 + 3 * k + 2) + 1 := h₂ (6 + 3 * k + 2) h6
        rw [show a (6 + 3 * k + 2) = 1 by omega] at h7
        have h8 : 6 + 3 * (k + 1) = 6 + 3 * k + 3 := by ring
        rw [h8]
        omega
      exact h5

  have h33 : a 99 = 4 := by
    have h44 : 99 = 6 + 3 * (31 : ℕ) := by omega
    rw [h44]
    apply cycle_lemma 31

  exact h33