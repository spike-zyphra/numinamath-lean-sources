import Mathlib

theorem number_theory_118641 (n : ℕ) (h : n > 0) (a : Fin 28 → ℕ)
    (ha : ∀ i j, a i = a j → i = j) (h1 : ∃ k, ∀ i, a i = k + i)
    (h2 : ∑ i, a i = 23 * 28) :
    IsGreatest {x | ∃ i, a i = x} 35 := by
  rcases h1 with ⟨k, hk⟩
  have h3 : ∑ i : Fin 28, a i = 28 * k + 378 := by
    simp_all [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    <;> omega
  rw [h3] at h2
  all_goals omega