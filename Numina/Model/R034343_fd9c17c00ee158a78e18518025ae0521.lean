import Mathlib


theorem number_theory_189788 (a : Fin 7 → ℕ) (h : ∀ s : Finset (Fin 7), s.card = 6 → 5 ∣ ∑ i ∈ s, a i) :
    ∀ i, 5 ∣ a i := by
  have h1 := h ({1, 2, 3, 4, 5, 6} : Finset (Fin 7)) (by simp)
  have h2 := h ({0, 2, 3, 4, 5, 6} : Finset (Fin 7)) (by simp)
  have h3 := h ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)) (by simp)
  have h4 := h ({0, 1, 2, 4, 5, 6} : Finset (Fin 7)) (by simp)
  have h5 := h ({0, 1, 2, 3, 5, 6} : Finset (Fin 7)) (by simp)
  have h6 := h ({0, 1, 2, 3, 4, 6} : Finset (Fin 7)) (by simp)
  have h7 := h ({0, 1, 2, 3, 4, 5} : Finset (Fin 7)) (by simp)
  intro i
  have h8 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
    fin_cases i <;> simp
  rcases h8 with (r | r | r | r | r | r | r)
  · -- i = 0
    rw [r]
    simp [Finset.sum_insert, Finset.sum_singleton] at h1 h2 h3 h4 h5 h6 h7 ⊢
    omega
  · -- i = 1
    rw [r]
    simp [Finset.sum_insert, Finset.sum_singleton] at h1 h2 h3 h4 h5 h6 h7 ⊢
    omega
  · -- i = 2
    rw [r]
    simp [Finset.sum_insert, Finset.sum_singleton] at h1 h2 h3 h4 h5 h6 h7 ⊢
    omega
  · -- i = 3
    rw [r]
    simp [Finset.sum_insert, Finset.sum_singleton] at h1 h2 h3 h4 h5 h6 h7 ⊢
    omega
  · -- i = 4
    rw [r]
    simp [Finset.sum_insert, Finset.sum_singleton] at h1 h2 h3 h4 h5 h6 h7 ⊢
    omega
  · -- i = 5
    rw [r]
    simp [Finset.sum_insert, Finset.sum_singleton] at h1 h2 h3 h4 h5 h6 h7 ⊢
    omega
  · -- i = 6
    rw [r]
    simp [Finset.sum_insert, Finset.sum_singleton] at h1 h2 h3 h4 h5 h6 h7 ⊢
    omega