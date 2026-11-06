import Mathlib

theorem algebra_851 {w : ℕ} (hw : w > 7) (h : w * (w - 7) = (w - 3) * (w - 5)) :
    w * (w - 7) = 120 := by
  have eq1 : w ≥ 8 := by omega
  have eq3 : (w : ℕ) = 15 := by
    have eq1 : w ≥ 8 := by omega
    have eq11 : w * (w - 7) = (w - 3) * (w - 5) := h
    have eq6 : (w: ℕ) = 15 := by
      have h1 : (w : ℕ) * (w - 7) = (w - 3) * (w - 5) := h
      have h3 : w ≥ 8 := by omega
      have h4 : (w : ℕ) ≥ 8 := by omega
      have eq1 : (↑w : ℤ) * ((↑w : ℤ) - 7) = ((↑w : ℤ) - 3) * ((↑w : ℤ) - 5) := by 
        have h1 : (w : ℕ) * (w - 7) = (w - 3) * (w - 5) := h
        zify [show w ≥ 7 by omega, show w ≥ 3 by omega, show w ≥ 5 by omega] at h1 ⊢
        all_goals nlinarith
      have eq2 : (↑w : ℤ) = 15 := by
        nlinarith
      have eq3 : (w : ℕ) = 15 := by
        exact_mod_cast eq2
      exact eq3
    exact eq6
  have eq8 : w * (w - 7) = 120 := by
    have eq9 : w = 15 := eq3
    rw [eq9]
    all_goals
      norm_num
  exact eq8