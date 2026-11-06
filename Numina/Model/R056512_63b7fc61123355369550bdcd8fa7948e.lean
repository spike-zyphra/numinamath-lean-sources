import Mathlib

theorem algebra_149741 (v : Fin 1980 → ℝ × ℝ)
    (h₀ : ∀ s : Finset (Fin 1980), s.card = 1979 → ∃ x : Fin 1980,
      x ∉ s ∧ (Finset.sum s fun i => v i) = -v x)
    (h₁ : ∃ i j, i ≠ j ∧ ¬(v i ∣ v j)) :
    ∑ i : Fin 1980, v i = 0 := by
  have h2 := h₀ (Finset.univ \ {0}) (by
    native_decide
  )
  rcases h2 with ⟨x, hx1, hx2⟩
  have h3 : x = 0 := by
    have h4 : x ∉ (Finset.univ \ {0} : Finset (Fin 1980)) := hx1
    simp at h4 ⊢
    exact h4
  rw [h3] at hx2
  have h8 : ∑ i : Fin 1980, v i = 0 := by
    have h9 : ∑ i : Fin 1980, v i = Finset.sum (Finset.univ \ {0} : Finset (Fin 1980)) (fun i => v i) + v 0 := by
      simp [Finset.sum_eq_sum_diff_singleton_add, Finset.mem_singleton]
    rw [h9]
    rw [hx2]
    simp
  exact h8