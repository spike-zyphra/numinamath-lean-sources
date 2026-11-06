import Mathlib

theorem algebra_269371 {a : ℕ → ℤ} (ha1 : a 1 = 13) (ha2 : a 2 = 56)
    (han : ∀ n > 0, a (n + 1) = a n + a (n + 2)) : a 1934 = 56 := by

  have h3 : ∀ n > 0, a (n + 2) = a (n + 1) - a n := by
    intro n hn
    have eq1 := han n (show n > 0 by exact_mod_cast hn)
    simp [eq1] at *
    <;> linarith
  
  have h1 : ∀ n : ℕ, a (6 * n + 1) = 13 := by 
    intro n 
    induction n with
    | zero =>
      norm_num [ha1]
    | succ n ih =>
      have eq2 := h3 (6 * n + 1) (by linarith)
      have eq3 := h3 (6 * n + 2) (by linarith)
      have eq4 := h3 (6 * n + 3) (by linarith)
      have eq5 := h3 (6 * n + 4) (by linarith)
      have eq6 := h3 (6 * n + 5) (by linarith)
      have eq7 := h3 (6 * n + 6) (by linarith)
      simp [show 6 * (n + 1) + 1 = 6 * n + 7 by ring] at *
      norm_num at ih eq2 eq3 eq4 eq5 eq6 eq7 ⊢
      linarith [ih, eq2, eq3, eq4, eq5, eq6, eq7]
  
  have h2 : ∀ n : ℕ, a (6 * n + 2) = 56 := by 
    intro n 
    induction n with 
    | zero =>
      norm_num [ha2]
    | succ n ih =>
      have eq2 := h3 (6 * n + 1) (by linarith)
      have eq3 := h3 (6 * n + 2) (by linarith)
      have eq4 := h3 (6 * n + 3) (by linarith)
      have eq5 := h3 (6 * n + 4) (by linarith)
      have eq6 := h3 (6 * n + 5) (by linarith)
      have eq7 := h3 (6 * n + 6) (by linarith)
      simp [show 6 * (n + 1) + 2 = 6 * n + 8 by ring] at *
      norm_num at ih eq2 eq3 eq4 eq5 eq6 eq7 ⊢
      linarith [ih, eq2, eq3, eq4, eq5, eq6, eq7]

  have eq1934 : 1934 = 6 * 322 + 2 := by 
    norm_num

  calc 
    a 1934 = a (6 * 322 + 2) := by rw [eq1934]
    _ = 56 := by apply h2 322
  all_goals linarith
  all_goals linarith