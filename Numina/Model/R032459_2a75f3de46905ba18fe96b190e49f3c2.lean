import Mathlib


theorem number_theory_208004 (a : Fin 7 → ℕ) (ha : ∀ i, a i > 0)
    (h : ∏ i, (a i - 3) = 13 * ∏ i, a i) :
    False := by
  have h1 : (∏ i : Fin 7, (a i - 3)) ≤ (∏ i : Fin 7, (a i)) := by
    have h2 : ∀ i : Fin 7, (a i - 3) ≤ a i := by
      intro i
      have ha4 : a i > 0 := ha i
      omega
    have h3 : (∏ i : Fin 7, (a i - 3)) ≤ (∏ i : Fin 7, (a i)) := by
      apply Finset.prod_le_prod
      all_goals
        intro i hi
        specialize h2 i
        all_goals
          linarith
    exact h3
  have h3 : 13 * (∏ i : Fin 7, (a i)) ≤ (∏ i : Fin 7, (a i)) := by
    nlinarith [h, h1]
  have h4 : (∏ i : Fin 7, (a i)) > 0 := by
    apply Finset.prod_pos
    intro i hi
    have ha8 : a i > 0 := ha i
    linarith
  have h5 : (∏ i : Fin 7, (a i)) ≤ 0 := by
    omega
  linarith