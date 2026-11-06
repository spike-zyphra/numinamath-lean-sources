import Mathlib

theorem number_theory_247781 (a : Fin 3 → Fin 3 → ℤ) (S : ℤ)
    (h₀ : ∀ i, ∑ j : Fin 3, a i j = S)
    (h₁ : ∀ j, ∑ i : Fin 3, a i j = S)
    (h₂ : ∑ i : Fin 3, a i i = S)
    (h₃ : ∑ i : Fin 3, a i (2 - i) = S) :
    3 ∣ S := by 
  have eq0 := h₀ 0
  have eq1 := h₀ 1
  have eq2 := h₀ 2
  have eq3 := h₁ 0
  have eq4 := h₁ 1
  have eq5 := h₁ 2
  have eq6 := h₂
  have eq7 := h₃
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7
  omega