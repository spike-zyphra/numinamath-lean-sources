import Mathlib

theorem algebra_200256 (a : Fin 8 → ℝ) (h : ∀ i, a i = (a (i - 1) + a (i + 1)) / 2) :
    ¬(∀ i j, i ≠ j → a i ≠ a j) := by 
  intro h1
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h 3
  have eq5 := h 4
  have eq6 := h 5
  have eq7 := h 6
  have eq8 := h 7
  simp [Fin.sum_univ_succ, Fin.sum_univ_zero] at eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8
  have eq9 : a 0 = a 1 := by
    linarith
  have eq11 := h1 0 1 (by simp)
  tauto