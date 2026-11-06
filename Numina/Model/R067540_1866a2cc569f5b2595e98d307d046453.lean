import Mathlib

theorem number_theory_135809 (n : ℕ) (h₀ : n % 10 ≠ 0) (h₁ : Even n) (h₂ : 3 ∣ n) (h₃ : 5 ∣ n)
    (h₄ : (¬Even n ∧ ¬3 ∣ n ∧ ¬5 ∣ n) ∨ (Even n ∧ ¬3 ∣ n ∧ ¬5 ∣ n) ∨
      (¬Even n ∧ 3 ∣ n ∧ ¬5 ∣ n) ∨ (Even n ∧ 3 ∣ n ∧ ¬5 ∣ n)) :
    n % 10 = 5 := by
  rcases h₄ with (h | h | h | h)
  · 
    have heven := h₁
    have hneven := h.1
    exfalso
    exact hneven heven
  · 
    have h3 := h₂
    have hnot3 := h.2.1
    exfalso
    exact hnot3 h3
  · 
    have heven := h₁
    have hneven := h.1
    exfalso
    exact hneven heven
  · 
    have h5 := h₃
    have hnot5 := h.2.2
    exfalso
    exact hnot5 h5