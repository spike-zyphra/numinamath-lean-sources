import Mathlib

theorem algebra_2434 {a b : ℝ}
    (ha : IsLeast {x | ∃ n : ℕ, x = -5 ∧ n = 0 ∨ x = -1 ∧ n = 1 ∨ x = 0.1 ∧ n = 2 ∨ x = -0.001 ∧ n = 3 ∨ x = -8 ∧ n = 4 ∨ x = -12.5 ∧ n = 5} a)
    (hb : IsGreatest {x | ∃ n : ℕ, x = -4 ∧ n = 0 ∨ x = -1 ∧ n = 1 ∨ x = -2.5 ∧ n = 2 ∨ x = -0.01 ∧ n = 3 ∨ x = -3.75 ∧ n = 4 ∨ x = -15 ∧ n = 5} b) :
    a / b = 1250 := by
  have ha1 : a = -12.5 := by
    have h112 : a ∈ {x | ∃ n : ℕ, x = -5 ∧ n = 0 ∨ x = -1 ∧ n = 1 ∨ x = 0.1 ∧ n = 2 ∨ x = -0.001 ∧ n = 3 ∨ x = -8 ∧ n = 4 ∨ x = -12.5 ∧ n = 5} := ha.1
    have h113 : ∀ x ∈ {x | ∃ n : ℕ, x = -5 ∧ n = 0 ∨ x = -1 ∧ n = 1 ∨ x = 0.1 ∧ n = 2 ∨ x = -0.001 ∧ n = 3 ∨ x = -8 ∧ n = 4 ∨ x = -12.5 ∧ n = 5}, a ≤ x := by 
      apply ha.2
    have h1100 := h113 (-12.5) (by norm_num)
    have h1111 : a = -5 ∨ a = -1 ∨ a = 0.1 ∨ a = -0.001 ∨ a = -8 ∨ a = -12.5 := by
      rcases h112 with ⟨n, hn⟩
      rcases hn with (hs | hs | hs | hs | hs | hs)
      all_goals
        norm_num at hs ⊢
        all_goals
          try { tauto }
    rcases h1111 with (h1111 | h1111 | h1111 | h1111 | h1111 | h1111)
    · -- Case a = -5
      linarith
    · -- Case a = -1
      linarith
    · -- Case a = 0.1
      linarith
    · -- Case a = -0.001
      linarith
    · -- Case a = -8
      linarith
    · -- Case a = -12.5
      linarith

  have hb1 : b = -0.01 := by
    have h112 : b ∈ {x | ∃ n : ℕ, x = -4 ∧ n = 0 ∨ x = -1 ∧ n = 1 ∨ x = -2.5 ∧ n = 2 ∨ x = -0.01 ∧ n = 3 ∨ x = -3.75 ∧ n = 4 ∨ x = -15 ∧ n = 5} := hb.1
    have h113 : ∀ x ∈ {x | ∃ n : ℕ, x = -4 ∧ n = 0 ∨ x = -1 ∧ n = 1 ∨ x = -2.5 ∧ n = 2 ∨ x = -0.01 ∧ n = 3 ∨ x = -3.75 ∧ n = 4 ∨ x = -15 ∧ n = 5}, x ≤ b := by 
      apply hb.2
    have h1100 := h113 (-0.01) (by norm_num)
    have h1111 : b = -4 ∨ b = -1 ∨ b = -2.5 ∨ b = -0.01 ∨ b = -3.75 ∨ b = -15 := by
      rcases h112 with ⟨n, hn⟩
      rcases hn with (hs | hs | hs | hs | hs | hs)
      all_goals
        norm_num at hs ⊢
        all_goals
          try { tauto }
    rcases h1111 with (h1111 | h1111 | h1111 | h1111 | h1111 | h1111)
    · -- Case b = -4
      linarith
    · -- Case b = -1
      linarith
    · -- Case b = -2.5
      linarith
    · -- Case b = -0.01
      linarith
    · -- Case b = -3.75
      linarith
    · -- Case b = -15
      linarith

  rw [ha1, hb1]
  norm_num