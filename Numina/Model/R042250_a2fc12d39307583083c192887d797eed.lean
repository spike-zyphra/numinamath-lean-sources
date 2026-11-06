import Mathlib

theorem number_theory_65751 (a : Fin 2016 → Fin 10)
  (h : 81 ∣ ∑ i : Fin 2016, a i * 10 ^ i.val) :
  ∀ j : Fin 2016, 81 ∣ ∑ i : Fin 2016, a (j - i) * 10 ^ i.val := by
  intro j
  have h1 : 81 ∣ ∑ i : Fin 2016, a i * 10 ^ i.val := h
  have h2 : 81 ∣ ∑ i : Fin 2016, a (j - i) * 10 ^ i.val := by
    simp [Fin.sum_univ_eq_sum_range] at h ⊢
    all_goals omega
  exact h2