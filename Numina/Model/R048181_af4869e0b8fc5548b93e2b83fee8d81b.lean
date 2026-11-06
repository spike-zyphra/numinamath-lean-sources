import Mathlib

theorem algebra_197148 {f : ℝ → ℝ} (hf0 : f 0 = 1) (hfx : ∀ x, f (x + 2) = f x + 4 * x + 2) :
    f 1000 = 999001 := by
  have h1 : ∀ (n : ℕ), f ( (↑n : ℝ) * 2 ) = 1 + (↑n : ℝ) ^ 2 * 4 - (↑n : ℝ) * 2 := by
    intro n
    induction n with
    | zero =>
      simp [hf0]
      all_goals norm_num
    | succ n ih =>
      have eq1 : (↑(n + 1 : ℕ) : ℝ) * 2 = (↑n * (2 : ℝ) ) + 2 := by
        simp at *
        <;> ring
      rw [eq1]
      have eq2 := hfx ( (↑n * (2 : ℝ) ) )
      rw [eq2]
      rw [ih]
      field_simp
      ring_nf
  have h2 := h1 500
  norm_num at h2 ⊢
  linarith [h2]