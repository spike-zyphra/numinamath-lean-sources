import Mathlib

theorem number_theory_271091 (a b c d e k : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e)
    (h₁ : a < b ∧ b < c ∧ c < d ∧ d < e)
    (h₂ : |a - b| = 2 ∧ |a - c| = 4 ∧ |a - d| = 5 ∧ |a - e| = 7)
    (h₃ : |b - c| = 8 ∧ |b - d| = k ∧ |b - e| = 13 ∧
      |c - d| = 15 ∧ |c - e| = 17 ∧ |d - e| = 19) :
    k = 12 := by
  rcases h₂ with ⟨h₂1, h₂2, h₂3, h₂4⟩
  rcases h₃ with ⟨h₃1, h₃2, h₃3, h₃4, h₃5, h₃6⟩
  have h4 : a < b := h₁.1
  have h5 : b < c := h₁.2.1
  have h6 : c < d := h₁.2.2.1
  have h7 : d < e := h₁.2.2.2
  have h8 : |a - b| = b - a := by
    rw [abs_of_neg (show (a - b : ℝ) < 0 by linarith)]
    all_goals linarith
  have h9 : b - a = 2 := by
    linarith [h₂1, h8]
  have h10 : |a - c| = c - a := by
    rw [abs_of_neg (show (a - c : ℝ) < 0 by nlinarith)]
    all_goals linarith
  have h11 : c - a = 4 := by
    linarith [h₂2, h10]
  have h12 : |a - d| = d - a := by 
    rw [abs_of_neg (show (a - d : ℝ) < 0 by nlinarith)]
    all_goals linarith
  have h13 : d - a = 5 := by 
    linarith [h₂3, h12]
  have h14 : |a - e| = e - a := by 
    rw [abs_of_neg (show (a - e : ℝ) < 0 by nlinarith)]
    all_goals linarith
  have h15 : e - a = 7 := by 
    linarith [h₂4, h14]
  have h16 : |b - c| = c - b := by 
    rw [abs_of_neg (show (b - c : ℝ) < 0 by nlinarith)]
    all_goals linarith
  have h17 : c - b = 8 := by 
    linarith [h₃1, h16]
  nlinarith