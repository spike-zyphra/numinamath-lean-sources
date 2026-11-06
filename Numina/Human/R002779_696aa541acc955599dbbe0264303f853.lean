import Mathlib

theorem algebra_111921
  {a b c d : ℝ}
  (f : ℝ → ℝ) (g : ℝ → ℝ)(f1 : ℝ → ℝ) (g1 : ℝ → ℝ)
  (hf : f = fun x => a * x ^ 2 + b * x)
  (hg : g = fun x => c * x ^ 2 + d * x)
  (hf1 : f1 = fun x => a * x + b)
  (hg1 : g1 = fun x => c * x + d)
  (hfg : ∃ x, x < 0 ∧ f x = g x ∧ g x = f1 x ∧ f1 x = g1 x) :
  a * c ≠ 0 → b * c = a * d := by
  intro hac
  rcases hfg with ⟨x, ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩⟩

  simp at hac
  have ha := hac.1
  have hc := hac.2

  have : f x = f1 x := by linarith

  rw [hf, hf1] at this
  simp at this
  have : (a * x + b) * (x - 1) = 0 := by linarith
  simp at this

  rcases this with h5 | h6
  . have : x = - b / a := by
      field_simp
      linarith

    rw [h4, hg, hg1] at h3
    simp at h3
    have : (c * x + d) * (x - 1) = 0 := by linarith
    simp at this
    rcases this with h5 | h6
    . rw [this] at h5
      field_simp at h5
      linarith
    . linarith

  . linarith
