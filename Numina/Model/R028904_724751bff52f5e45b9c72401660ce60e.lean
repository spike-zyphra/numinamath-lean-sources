import Mathlib

theorem number_theory_279075 (a b c d e : ℕ) (h₀ : a < b) (h₁ : b < c) (h₂ : c < d)
    (h₃ : d < e) (h₄ : e - a = 8) (h₅ : a * b = 12) (h₆ : c + d + e = 25) :
    (a = 2 ∧ b = 6 ∧ c = 7 ∧ d = 8 ∧ e = 10) ∨
    (a = 3 ∧ b = 4 ∧ c = 5 ∧ d = 9 ∧ e = 11) ∨
    (a = 3 ∧ b = 4 ∧ c = 6 ∧ d = 8 ∧ e = 11) := by
  have h₇ : a ≤ 3 := by
    by_contra h
    push_neg at h
    have : a * b > 12 := by
      nlinarith [show b ≥ 4 from by nlinarith]
    nlinarith
  have h₉ : a > 0 := by
    by_contra h
    push_neg at h
    have : a = 0 := by 
      omega
    rw [this] at h₅
    nlinarith
  interval_cases a <;> try { 
    have h₉ : b ≤ 12 := by 
      nlinarith
    interval_cases b <;> 
      try { 
        omega 
      }
    <;> try { 
          -- Now, e = a + 8 from h₄: e - a = 8
          omega 
        }
  }