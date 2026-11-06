import Mathlib

theorem algebra_210162 (l t : ℕ) (hl : l ≠ 0) (ht : t ≠ 0)
    (h : (3 / 5 : ℚ) * l = (2 / 3 : ℚ) * t) :
    l ≥ 10 := by 
  have h1 : (l : ℚ) * 9 = (t : ℚ) * 10 := by 
    linarith [h]
  have h2 : (9 * (l : ℕ) : ℚ) = (10 * (t : ℕ) : ℚ) := by
    have eq1 := h1
    ring_nf at eq1 ⊢
    exact_mod_cast eq1
  have eq3 : 9 * (l : ℕ) = 10 * (t : ℕ) := by 
    exact_mod_cast h2 
  omega