import Mathlib

theorem algebra_281572 {c t : ℕ} (ht : t ≠ 0) (h : c = t * (1 + 25 / 100 : ℝ)) :
    c * 4 = t * 5 := by
  have h1 : (c : ℝ) = (t : ℝ) * (1 + 25 / 100 : ℝ) := by
    simpa using h
  have h2 : (c : ℝ) = (t : ℝ) * (5 / 4 : ℝ) := by
    norm_num at h1 ⊢
    linarith
  have h3 : (c : ℝ) * 4 = (t : ℝ) * 5 := by
    linarith [h2]
  exact_mod_cast h3