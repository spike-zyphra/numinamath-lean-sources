import Mathlib

theorem algebra_235653 {a : ℕ → ℝ} (ha1 : a 1 = 1) (han0 : ∀ n > 0, a n ≠ 0)
    (han : ∀ n ≥ 2, a n + 2 * a n * a (n - 1) - a (n - 1) = 0) :
    ∀ n > 0, a n = 1 / (2 * n - 1) := by
  intro n hn
  have h1 : ∀ n : ℕ, n > 0 → a n = 1 / (2 * (n : ℝ) - 1) := by
    intro n hn
    induction n with
    | zero =>
      exfalso
      linarith
    | succ n ih =>
      cases n with
      | zero =>
        rw [ha1]
        norm_num
      | succ n =>
        have eq2 := han (n + 2) (by linarith)
        have eq3 : (n + 2 : ℕ) - 1 = n + 1 := by
          omega
        rw [eq3] at eq2
        have eq7 : a (n + 1) ≠ 0 := han0 (n + 1) (by linarith)
        have eq8 : a (n + 2) = a (n + 1) / (1 + 2 * a (n + 1)) := by
          have eq9 : a (n + 2) * (1 + 2 * a (n + 1)) = a (n + 1) := by
            nlinarith
          have eq10 : 1 + 2 * a (n + 1) ≠ 0 := by
            have eq15 : a (n + 1) = 1 / (2 * (↑n + 1 : ℝ) - 1) := by
              specialize ih (by linarith)
              simpa using ih
            by_contra h
            have h5 : 1 + 2 * a (n + 1) = 0 := by linarith
            rw [eq15] at h5
            field_simp [(show (2 * (↑n + 1 : ℝ) - 1) ≠ 0 by
              by_contra h'
              have h6 : (2 * (↑n + 1 : ℝ) - 1) = 0 := by linarith
              have : (n : ℝ) = 0 := by nlinarith
              have : n = 0 := by
                exact_mod_cast this
              rw [this] at h6
              norm_num at h6
            )] at h5
            all_goals
            nlinarith [sq_nonneg ((↑n : ℝ)), sq_nonneg ((↑n + 1 : ℝ))]
          field_simp at eq9 ⊢
          <;> nlinarith
        have eq9 : a (n + 1) = 1 / (2 * (↑n + 1 : ℝ) - 1) := by
          specialize ih (by linarith)
          simpa using ih
        rw [eq8]
        rw [eq9]
        field_simp [(show (2 * (↑n + 1 : ℝ) - 1) ≠ 0 by
          by_contra h'
          have h6 : (2 * (↑n + 1 : ℝ) - 1) = 0 := by linarith
          have : (n : ℝ) = 0 := by nlinarith
          have : n = 0 := by
            exact_mod_cast this
          rw [this] at h6
          norm_num at h6
        )]
        <;> ring_nf
  specialize h1 n hn
  simpa using h1