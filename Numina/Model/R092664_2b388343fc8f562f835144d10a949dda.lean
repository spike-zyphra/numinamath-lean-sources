import Mathlib

theorem algebra_207605 (v : Fin 1980 → ℝ × ℝ)
    (hsum : ∀ s : Finset (Fin 1980), s.card = 1979 → ∃ t : Fin 1980, t ∉ s ∧
      (∑ i ∈ s, v i) = -v t)
    (hmul : ¬∀ i j, i ≠ j → v i ∣ v j) :
    ∑ i : Fin 1980, v i = 0 := by
  have h1 := hsum (Finset.univ \ {0}) (by
    native_decide
  )
  rcases h1 with ⟨t, ht1, ht2⟩
  have ht3 : t = 0 := by
    simp [Finset.mem_compl] at ht1 
    simpa using ht1

  rw [ht3] at ht2
  have h3 : ∑ i ∈ Finset.univ \ {0}, v i = -v 0 := ht2 
  have h4 : ∑ i : Fin 1980, v i = ∑ i ∈ Finset.univ \ {0}, v i + v 0 := by
    simp [Finset.sum_eq_zero]
  <;> try contradiction
  rw [h4, h3]
  simp