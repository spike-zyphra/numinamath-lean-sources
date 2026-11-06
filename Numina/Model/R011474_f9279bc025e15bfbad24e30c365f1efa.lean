import Mathlib


theorem number_theory_25084 (a b c d : ℤ) (h₀ : a > b) (h₁ : b > c) (h₂ : c > d) (h₃ : d > 0) (h : a * c + b * d = (b + d + a - c) * (b + d - a + c)) :
    ¬Prime (a * b + c * d) := by
  have h₄ : a ^ 2 - a * c + c ^ 2 = b ^ 2 + b * d + d ^ 2 := by
    linarith
  have h₅ : a * b + c * d > 0 := by
    nlinarith
  have h₆ : a * c + b * d > 1 := by
    nlinarith
  have h₇ : (a * b + c * d) * (a * d + b * c) = (a * c + b * d) * (a ^ 2 - a * c + c ^ 2) := by
    calc
      _ = (a * c) * (b ^ 2 + b * d + d ^ 2) + (b * d) * (a ^ 2 - a * c + c ^ 2) := by ring
      _ = (a * c) * (a ^ 2 - a * c + c ^ 2) + (b * d) * (a ^ 2 - a * c + c ^ 2) := by rw [h₄]
      _ = (a * c + b * d) * (a ^ 2 - a * c + c ^ 2) := by ring
  by_contra hp
  have hp1 : Prime (a * b + c * d) := by exact_mod_cast hp
  have h₈ : (a * b + c * d) ∣ (a * c + b * d) ∨ (a * b + c * d) ∣ (a ^ 2 - a * c + c ^ 2) := by
    have h₆ : (a * b + c * d) ∣ (a * c + b * d) * (a ^ 2 - a * c + c ^ 2) := by
      use a * d + b * c
      all_goals linarith [h₇]
    have h₇ : (a * b + c * d) ∣ (a * c + b * d) ∨ (a * b + c * d) ∣ (a ^ 2 - a * c + c ^ 2) := by
      apply (Prime.dvd_mul hp1).mp 
      exact h₆
    assumption
  cases h₈ with
  | inl h₈ =>
    have h₈₃ : a * b + c * d ∣ a * c + b * d := h₈
    have h₈₄ : a * b + c * d ≤ a * c + b * d := by 
      exact Int.le_of_dvd (show a * c + b * d > 0 by nlinarith) h₈₃
    have eq : a * b = a * c := by 
      nlinarith
    have : b = c := by
      nlinarith [eq, show a > 0 by nlinarith, show a - c ≠ 0 by nlinarith]
    omega
  | inr h₈ =>
    have h₈₃ : a * b + c * d ∣ a ^ 2 - a * c + c ^ 2 := h₈
    have h₈₄ : a * b + c * d ≤ a ^ 2 - a * c + c ^ 2 := by 
      exact Int.le_of_dvd (show a ^ 2 - a * c + c ^ 2 > 0 by nlinarith) h₈₃
    nlinarith [mul_pos (show 0 < (a - c) by linarith) (show 0 < (b - d) by linarith), mul_pos (show 0 < (a - c) by linarith) (show 0 < (c - d) by linarith), mul_pos (show 0 < (b - c) by linarith) (show 0 < (c - d) by linarith), sq_pos_of_pos (show 0 < a - c by nlinarith), sq_pos_of_pos (show 0 < c - d by nlinarith)]