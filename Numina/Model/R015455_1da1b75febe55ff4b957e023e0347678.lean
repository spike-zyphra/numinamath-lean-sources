import Mathlib


theorem algebra_95400 (b j : Fin 4 → ℕ) (h : ∀i, b i ≤ 100 ∧ j i ≤ 100)
(hb : ∑ i, b i = 78 * 4) (hj : j 0 = b 0 + 10 ∧ j 1 = b 1 - 10 ∧ j 2 = b 2 + 20 ∧ j 3 = b 3 + 20) :
(∑ i, j i) / 4 - (∑ i, b i) / 4 = 10 := by 
  rcases hj with ⟨hj0, hj1, hj2, hj3⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  rcases h0 with ⟨hb0, hj00⟩
  rcases h1 with ⟨hb1, hj11⟩
  rcases h2 with ⟨hb2, hj22⟩
  rcases h3 with ⟨hb3, hj33⟩
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, hj0, hj1, hj2, hj3] at hb ⊢
  omega