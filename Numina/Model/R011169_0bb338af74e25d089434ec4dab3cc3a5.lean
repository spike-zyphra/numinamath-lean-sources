import Mathlib
theorem algebra_611256 (a : ℕ → ℝ) (h1 : a 1 = 1) (h2 : a 2 = 0) (hn : ∀ n : ℕ, n > 0 → a (n + 1) = a n + a (n + 2) / 2) : a 2004 = (-4) ^ 501:= by
  have h3 : ∀ n : ℕ, a (4 * n + 4) = (-4 : ℝ) ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      norm_num
      have eq1 := hn 1 (by norm_num)
      have eq2 := hn 2 (by norm_num)
      have eq3 := hn 3 (by norm_num)
      norm_num [h1, h2] at eq1 eq2 eq3 ⊢
      linarith
    | succ n ih =>
      have eq1 := hn (4 * n + 4) (by omega)
      have eq2 := hn (4 * n + 5) (by omega)
      have eq3 := hn (4 * n + 6) (by omega)
      have eq4 := hn (4 * n + 7) (by omega)
      have eq5 : a (4 * n + 6) = 2 * a (4 * n + 5) - 2 * a (4 * n + 4) := by
        have h4 := hn (4 * n + 4) (by omega)
        simp [show 4 * n + 4 > 0 by omega] at h4 ⊢
        linarith
      have eq6 : a (4 * n + 7) = 2 * a (4 * n + 6) - 2 * a (4 * n + 5) := by
        have h4 := hn (4 * n + 5) (by omega)
        simp [show 4 * n + 5 > 0 by omega] at h4 ⊢
        linarith
      have eq7 : a (4 * n + 8) = 2 * a (4 * n + 7) - 2 * a (4 * n + 6) := by
        have h4 := hn (4 * n + 6) (by omega)
        simp [show 4 * n + 6 > 0 by omega] at h4 ⊢
        linarith
      have eq8 : a (4 * n + 5) = a (4 * n + 4) + a (4 * n + 6) / 2 := by
        have h4 := hn (4 * n + 4) (by omega)
        simpa using h4
      have eq9 : a (4 * n + 8) = -4 * a (4 * n + 4) := by
        linarith [eq5, eq6, eq7, eq8]
      simp [show 4 * (n + 1) + 4 = (4 * n + 8) by omega] at ih ⊢
      rw [eq9]
      rw [ih]
      ring_nf
  have h4 : 2004 = 4 * 500 + 4 := by
    omega
  rw [h4]
  specialize h3 500
  norm_num at h3 ⊢
  linarith