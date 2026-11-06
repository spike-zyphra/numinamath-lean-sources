import Mathlib

theorem number_theory_211399 (a b c d e : ℕ) (h₀ : a < b) (h₁ : b < c) (h₂ : c < d)
    (h₃ : d < e) (h₄ : a * b > 25) (h₅ : d * e < 75) :
    a = 5 ∧ b = 6 ∧ c = 7 ∧ d = 8 ∧ e = 9 := by
  have h7 : a ≤ 5 := by
    by_contra h
    push_neg at h
    have ha1 : a ≥ 6 := by linarith
    have hb1 : b ≥ 7 := by
      omega
    have hc1 : c ≥ 8 := by
      omega
    have hd1 : d ≥ 9 := by
      omega
    have he1 : e ≥ 10 := by
      omega
    nlinarith
  have h8 : a = 5 := by
    have h9 : a ≤ 5 := h7
    by_cases h10 : a < 5
    · -- Assume a < 5, so a = 0, 1, 2, 3, 4. Show a contradiction.
      have h11 : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by
        omega
      rcases h11 with (r | r | r | r | r)
      · -- a = 0
        rw [show a = 0 by omega] at h₄
        all_goals
        omega
      · -- a = 1
        rw [show a = 1 by omega] at h₄
        have h10 : b ≥ 26 := by
          nlinarith
        have h10' : d ≥ 28 := by
          omega
        have h10'' : e ≥ 29 := by
          omega
        nlinarith
      · -- a = 2
        rw [show a = 2 by omega] at h₄
        have h10 : b ≥ 13 := by
          nlinarith
        have h10' : d ≥ 15 := by
          omega
        have h10'' : e ≥ 16 := by
          omega
        nlinarith
      · -- a = 3
        rw [show a = 3 by omega] at h₄
        have h10 : b ≥ 9 := by
          nlinarith
        have h10' : d ≥ 11 := by
          omega
        have h10'' : e ≥ 12 := by
          omega
        nlinarith
      · -- a = 4
        rw [show a = 4 by omega] at h₄
        have h10 : b ≥ 7 := by
          nlinarith
        have h10' : d ≥ 9 := by
          omega
        have h10'' : e ≥ 10 := by
          omega
        nlinarith
    · -- a ≥ 5. Since a ≤ 5, so a = 5.
      have h11 : a = 5 := by
        omega
      exact h11
  have ha5 : a = 5 := h8
  have hb6 : b = 6 := by
    rw [show a = 5 by omega] at h₄
    have hb6 : b ≥ 6 := by
      nlinarith
    have hb7 : b < 7 := by
      by_contra h
      push_neg at h
      have hb1 : b ≥ 7 := by
        omega
      have hc1 : c ≥ 8 := by
        omega
      have hd1 : d ≥ 9 := by
        omega
      have he1 : e ≥ 10 := by
        omega
      nlinarith
    omega
  have hc7 : c = 7 := by
    have hb6 : b = 6 := hb6
    have hc7 : c ≥ 7 := by
      omega
    have hc8 : c < 8 := by
      by_contra h
      push_neg at h
      have hc1 : c ≥ 8 := by
        omega
      have hd1 : d ≥ 9 := by
        omega
      have he1 : e ≥ 10 := by
        omega
      nlinarith
    omega
  have hd8 : d = 8 := by
    have hc7 : c = 7 := hc7
    have hd8 : d ≥ 8 := by
      omega
    have hd9 : d < 9 := by
      by_contra h
      push_neg at h
      have hd1 : d ≥ 9 := by
        omega
      have he1 : e ≥ 10 := by
        omega
      nlinarith
    omega
  have he9 : e = 9 := by
    have hd8 : d = 8 := hd8
    have he9 : e ≥ 9 := by
      omega
    have he10 : e < 10 := by
      by_contra h
      push_neg at h
      have he1 : e ≥ 10 := by
        omega
      nlinarith
    omega
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩