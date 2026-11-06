import Mathlib

theorem algebra_227691 {f : ℝ → ℝ} (h : ∀ x, 0 ≤ x → f (x + 1) + 1 = f x + 20 / ((x + 1) * (x + 2))) (hf : f 0 = 2019) :
    2019 / f 2019 = 101 := by

  have eq1 : ∀ (x : ℕ), f (↑x : ℝ) = 2019 - ↑x + (20 * ↑x) / (↑x + 1) := by
    intro x 
    induction x with 
    | zero => 
      norm_num 
      all_goals linarith [hf]
    | succ x ih =>
      have eq2 := h (↑x : ℝ) (by
        exact_mod_cast (show (0 : ℕ) ≤ x by omega)
      )
      simp at eq2 ⊢ 
      rw [ih] at eq2 
      field_simp at eq2 ⊢ 
      ring_nf at eq2 ⊢ 
      <;> nlinarith 
  have eq2019 : f 2019 = (2019 / 101 : ℝ) := by
    specialize eq1 2019 
    norm_num at eq1 ⊢ 
    linarith 
  rw [eq2019]
  norm_num