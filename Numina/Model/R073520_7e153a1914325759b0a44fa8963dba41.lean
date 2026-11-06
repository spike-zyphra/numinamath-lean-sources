import Mathlib

theorem algebra_243240 : ¬∃ n : ℤ, (1 / 2 : ℝ) = n := by
  rintro ⟨n, hn⟩
  have h2 : (n : ℝ) = (1 / 2 : ℝ) := by 
    linarith
  have h3 : 2 * (n : ℝ) = 1 := by 
    linarith
  have h4 : 2 * (n : ℤ) = 1 := by 
    norm_num at h3 ⊢
    exact_mod_cast h3
  omega