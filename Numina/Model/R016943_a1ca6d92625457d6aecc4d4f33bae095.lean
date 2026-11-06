import Mathlib

theorem number_theory_317560 (a b : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9) (h₁ : 0 ≤ b ∧ b ≤ 9)
    (h₂ : ∃ n, n^2 = 1000 * a + 100 * a + 10 * b + b) :
    a + b = 11 := by
  rcases h₂ with ⟨n, hn⟩
  have h3 : n^2 ≥ 1000 := by
    have ha1 : 1 ≤ a := h₀.1
    have ha2 : a ≤ 9 := h₀.2
    have hb1 : 0 ≤ b := h₁.1
    have hb2 : b ≤ 9 := h₁.2
    nlinarith
  have h4 : n^2 ≤ 9999 := by
    have ha1 : 1 ≤ a := h₀.1
    have ha2 : a ≤ 9 := h₀.2
    have hb1 : 0 ≤ b := h₁.1
    have hb2 : b ≤ 9 := h₁.2
    nlinarith
  have h5 : n ≤ 99 := by
    nlinarith [show n^2 ≤ 9999 from h4]
  have h6 : n ≥ 32 := by
    by_contra h
    push_neg at h
    have h7 : n ≤ 31 := by linarith
    have h8 : n^2 < 1000 := by
      nlinarith [h7]
    nlinarith
  interval_cases n <;> omega