import Mathlib

theorem number_theory_213178 (a : Fin 7 → ℕ) (ha : ∀ s : Finset (Fin 7), s.card = 6 → 5 ∣ ∑ i ∈ s, a i) :
    ∀ i : Fin 7, 5 ∣ a i := by 
  have h1 := ha {1, 2, 3, 4, 5, 6} (by native_decide)
  have h2 := ha {0, 2, 3, 4, 5, 6} (by native_decide)
  have h3 := ha {0, 1, 3, 4, 5, 6} (by native_decide)
  have h4 := ha {0, 1, 2, 4, 5, 6} (by native_decide)
  have h5 := ha {0, 1, 2, 3, 5, 6} (by native_decide)
  have h6 := ha {0, 1, 2, 3, 4, 6} (by native_decide)
  have h7 := ha {0, 1, 2, 3, 4, 5} (by native_decide)
  intro i 
  fin_cases i <;> simp [Finset.sum_insert, Finset.sum_singleton] at h1 h2 h3 h4 h5 h6 h7 ⊢ <;> omega