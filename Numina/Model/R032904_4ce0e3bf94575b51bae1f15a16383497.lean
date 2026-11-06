import Mathlib

theorem algebra_96773 (a b c : ℕ) (h₀ : a + b + c = 444) (h₁ : c > b) (h₂ : b > a)
(h₃ : ∃ r : ℚ, b = a * r ∧ c = b * r) (hi : 9 ≤ b) (hj : 5 ≤ a) (hk : 25 ≤ c) (h₄ : ∃ d, b - 9 = a - 5 + d ∧ c - 25 = b - 9 + d) :
a = 108 := by
  rcases h₃ with ⟨r, hr₁, hr₂⟩
  rcases h₄ with ⟨d, h₅, h₆⟩
  have h₇ : (b : ℚ) = (a : ℚ) + 4 + (d : ℚ) := by
    have h13 : (b : ℚ) - 9 = (a : ℚ) - 5 + (d : ℚ) := by
      exact_mod_cast h₅
    nlinarith
  have h₈ : (c : ℚ) = (b : ℚ) + 16 + (d : ℚ) := by
    have h13 : (c : ℚ) - 25 = (b : ℚ) - 9 + (d : ℚ) := by
      exact_mod_cast h₆
    nlinarith
  have h₆₁ : (a : ℚ) + (b : ℚ) + (c : ℚ) = 444 := by 
    have h9 : (a + b + c : ℚ) = 444 := by
      exact_mod_cast h₀
    linarith
  have h₇₁ : (b : ℚ) = (a : ℚ) * r := by 
    simpa using hr₁
  have h₈₁ : (c : ℚ) = (b : ℚ) * r := by 
    simpa using hr₂
  have h10 : (a : ℚ) = 108 := by
    nlinarith [sq_pos_of_pos (show 0 < (2 : ℚ) by norm_num), sq_nonneg (r - 3 / 2 : ℚ),
      sq_nonneg ((a : ℚ) - 108 : ℚ), sq_nonneg ((d : ℚ) * 1 : ℚ),
      sq_pos_of_pos (show 0 < (1 : ℚ) by norm_num),
      mul_pos (show 0 < (1 : ℚ) by norm_num) (show 0 < (1 : ℚ) by norm_num)]
  have h12 : a = 108 := by
    exact_mod_cast h10
  exact h12