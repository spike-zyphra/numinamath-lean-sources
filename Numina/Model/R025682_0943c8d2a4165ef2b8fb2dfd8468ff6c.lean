import Mathlib

theorem algebra_10875
    (a : ℕ → ℝ)
    (h₀ : a 1 = 0)
    (h₁ : ∀ n ≥ 1, a (n + 1) = a n + 1 + 2 * Real.sqrt (1 + a n)) :
    a 2009 = 4036080 := by

  have h2 : ∀ n, a (n + 1) = (↑n + 1 : ℝ) ^ 2 - 1 := by
    intro n
    induction n with
    | zero =>
      norm_num [h₀]
    | succ n ih =>
      have h3 : a (n + 2) = a (n + 1) + 1 + 2 * Real.sqrt (1 + a (n + 1)) := by
        specialize h₁ (n + 1) (by linarith)
        simpa using h₁
      rw [h3]
      rw [ih]
      have h4 : Real.sqrt (1 + ((↑n + 1 : ℝ) ^ 2 - 1 : ℝ)) = (↑n + 1 : ℝ) := by
        have h5 : (1 + ((↑n + 1 : ℝ) ^ 2 - 1 : ℝ)) = (↑n + 1 : ℝ) ^ 2 := by
          ring_nf
        rw [h5]
        have h6 : Real.sqrt ((↑n + 1 : ℝ) ^ 2) = (↑n + 1 : ℝ) := by
          rw [Real.sqrt_sq (show 0 ≤ (↑n + 1 : ℝ) by positivity)]
        exact h6
      rw [h4]
      field_simp
      <;> ring_nf

  have eq1 : a 2009 = (↑(2008) + 1 : ℝ) ^ 2 - 1 := by
    specialize h2 2008
    norm_num at h2 ⊢
    linarith

  rw [eq1]
  norm_num