import Mathlib

theorem algebra_219473 {A : Polynomial ℝ → ℝ} (hA : ∀ P, A P = ∑ i in Finset.range (P.natDegree + 1), P.coeff i * (P.natDegree.choose i)) :
    ¬∃ f : ℕ → ℝ, ∀ P, A P = f P.natDegree := by
  intro h
  rcases h with ⟨f, hf⟩
  have eq1 := hf (0 : Polynomial ℝ)
  simp [hA] at eq1
  have eq0 := hf (Polynomial.C (1 : ℝ))
  simp [hA, Polynomial.natDegree_C] at eq0
  all_goals
    norm_num at eq0 eq1 
    all_goals
      linarith