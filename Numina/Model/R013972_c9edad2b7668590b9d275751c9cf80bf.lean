import Mathlib

theorem algebra_34028 (x : ℕ → ℝ) (h : ∀ n, 0 < n → x (n + 1) = (1 + 2 / n) * x n + 4 / n)
    (hx : x 1 = -1) : x 2000 = 2000998 := by

  have eq1 : ∀ (n : ℕ), x (n + 1) = ((↑n + 1 : ℝ) * (↑n + 2 : ℝ)) / 2 - 2 := by 
    intro n 
    induction n with
    | zero => 
      have eq2 : x 1 = -1 := hx
      norm_num at eq2 ⊢
      linarith
    | succ n ih =>
      have h1 := h (n + 1) (by linarith)
      rw [show n + 1 + 1 = n + 2 by omega] at h1 
      rw [ih] at h1 
      field_simp at h1 ⊢
      ring_nf at h1 ⊢
      <;> nlinarith 
  have eq3 : x 2000 = ((↑(1999 : ℕ) + 1 : ℝ) * (↑(1999 : ℕ) + 2 : ℝ)) / 2 - 2 := by 
    have eq4 : 1999 + 1 = 2000 := by 
      omega 
    specialize eq1 1999
    rw [eq4] at eq1 
    linarith 
  rw [eq3] 
  norm_num