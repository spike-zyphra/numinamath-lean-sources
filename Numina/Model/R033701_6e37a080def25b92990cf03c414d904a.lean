import Mathlib

theorem algebra_288675 {f : ℝ → ℝ} (h : ∀ x, f (x + 1) = f x + 2 * x + 3) (hf : f 0 = 1) :
    f 2018 = 4076361 := by
  have eq1 : ∀ (n : ℕ), f (↑n : ℝ) = (↑n + 1 : ℝ) ^ 2 := by
    intro n
    induction n with
    | zero =>
      norm_num [hf]
    | succ n ih =>
      have eq2 := h (↑n : ℝ)
      have eq3 : (↑n + 1 : ℝ) ^ 2 + 2 * (↑n : ℝ) + 3 = ((↑n + 1 + 1 : ℝ) ) ^ 2 := by
        ring_nf
      rw [ih] at eq2
      rw [eq3] at eq2
      simp [pow_two] at *
      <;> linarith [eq2]
  specialize eq1 2018
  norm_num at eq1 ⊢
  linarith