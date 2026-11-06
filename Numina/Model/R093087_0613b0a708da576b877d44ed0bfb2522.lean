import Mathlib

theorem number_theory_222476 (n : ℤ) (h : ∃ a b c, n = a^2 + b^2 + c^2) :
    ∃ d e f g : ℚ, n = d^2 + e^2 + f^2 + g^2 := by 
  rcases h with ⟨a, b, c, hn⟩
  use (a : ℚ), (b : ℚ), (c : ℚ), (0 : ℚ)
  have h1 : (n : ℚ) = (a : ℚ) ^ 2 + (b : ℚ) ^ 2 + (c : ℚ) ^ 2 := by 
    exact_mod_cast (by linarith)
  norm_num [h1]
  all_goals norm_num
  all_goals linarith