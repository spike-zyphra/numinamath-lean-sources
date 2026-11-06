import Mathlib

theorem algebra_141110 {f : ℝ → ℝ} (hf : ∃ a b c, f = fun x => a*x^2 + b*x + c)
    (g : ℝ → ℝ) (hg : g = fun x => 2^x * f x) (h : ∀ x, g (x + 1) - g x = 2^(x + 1) * x^2) :
    f = fun x => 2*x^2 - 8*x + 12 := by

  rcases hf with ⟨a, b, c, hf⟩
  have eq1 := h 0
  simp [hg, hf] at eq1
  have eq2 := h 1
  norm_num [hg, hf] at eq2
  have eq3 := h 2
  norm_num [hg, hf] at eq3
  have eq4 := h 3
  norm_num [hg, hf] at eq4
  have ha : a = 2 := by
    ring_nf at eq1 eq2 eq3 eq4
    linarith
  have hb : b = -8 := by
    ring_nf at eq1 eq2 eq3 eq4
    linarith
  have hc : c = 12 := by
    ring_nf at eq1 eq2 eq3 eq4
    linarith
  funext x
  simp [hf, ha, hb, hc]
  <;> ring