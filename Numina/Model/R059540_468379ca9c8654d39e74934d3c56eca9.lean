import Mathlib

theorem number_theory_149924 (m : ℕ) (a : Fin m → ℕ) (ha : ∀ i, a i ∈ Finset.Icc 1 m)
    (h : ∀ s : Finset (Fin m), ¬(∑ i ∈ s, a i) % (m + 1) = 0) :
    ∃ x, ∀ i, a i = x := by 
  have h1 := h ∅
  simp at h1
  all_goals trivial