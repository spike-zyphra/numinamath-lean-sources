import Mathlib

theorem inequalities_209223 :
    IsLeast {n : ℕ | ∀ x y z : ℝ, (x^2 + y^2 + z^2)^2 ≤ n * (x^4 + y^4 + z^4)} 3 := by 
  constructor
  · -- Show that 3 is in the set
    intro x y z
    have h : (x^2 + y^2 + z^2)^2 ≤ (3 : ℝ) * (x^4 + y^4 + z^4) := by
      nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2)]
    norm_num at h ⊢
    linarith
  · -- Show that 3 is the smallest
    intro n hn
    have h1 := hn (1 / 2 : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ)
    norm_num at h1 ⊢
    have : n ≥ 3 := by
      by_contra h
      push_neg at h
      have : n ≤ 2 := by linarith
      have h2 : (n : ℝ) ≤ (2 : ℝ) := by 
        exact_mod_cast this
      nlinarith
    linarith