import Mathlib

theorem algebra_327714 {f : ℝ → ℝ} (hf : ∃ a b c, f = fun x => a*x^2 + b*x + c)
    (h0 : f 0 = 0) (h1 : ∀ x, f (x + 2) = f x + x + 2) :
    f = fun x => (1/4)*x^2 + (1/2)*x := by

  rcases hf with ⟨a, b, c, h_def⟩
  have hc : c = 0 := by
    simp [h_def] at h0
    linarith

  have eq1 := h1 0
  simp [h_def] at eq1
  rw [hc] at eq1

  have eq2 := h1 1
  simp [h_def] at eq2
  rw [hc] at eq2

  have eq3 := h1 2
  simp [h_def] at eq3
  rw [hc] at eq3

  have h2 : a = 1 / 4 := by
    nlinarith

  have h3 : b = 1 / 2 := by
    nlinarith [h2]

  ext x
  simp [h_def, h2, h3, hc]
  <;> ring_nf <;> norm_num