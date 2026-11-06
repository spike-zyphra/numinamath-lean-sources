import Mathlib

theorem number_theory_294505 (p a pa : Fin 6 → ℕ)
    (h₀ : ∀ i, pa i = ∑ j in Finset.univ \ {i}, a j)
    (h₁ : ∀ i, a i = ∑ j in Finset.univ \ {i}, p j) :
    31 ∣ ∑ i, (p i + a i + pa i) := by
  have eq1 : ∑ i, pa i = 5 * ∑ i, a i := by 
    have h2 : ∀ i, pa i + a i = ∑ j : Fin 6, a j := by
      intro i 
      specialize h₀ i
      rw [h₀]
      rw [Finset.sum_eq_sum_diff_singleton_add (show i ∈ Finset.univ by simp)]
      all_goals simp
      <;> try { tauto }
    have eq2 : ∀ i, pa i + a i = ∑ j : Fin 6, a j := h2
    have eq3 : ∑ i : Fin 6, (pa i + a i) = ∑ i : Fin 6, (∑ j : Fin 6, a j) := by 
      apply Finset.sum_congr 
      . rfl 
      . intro i hi 
        exact eq2 i 
    simp at eq3 ⊢
    <;> try { tauto }
    all_goals try { tauto }
    all_goals try { tauto }
    have eq4 : ∑ i : Fin 6, (pa i + a i) = ∑ i : Fin 6, pa i + ∑ i : Fin 6, a i := by 
      simp [Finset.sum_add_distrib]
    have eq5 : ∑ i : Fin 6, (∑ j : Fin 6, a j) = 6 * ∑ j : Fin 6, a j := by 
      simp [Finset.sum_const, Finset.card_univ]
      all_goals try { try { tauto } }
      all_goals try { try { tauto } }
      all_goals try { try { tauto } }
    linarith [eq3, eq4, eq5]
  have eq2 : ∑ i, a i = 5 * ∑ i, p i := by 
    have h2 : ∀ i, a i + p i = ∑ j : Fin 6, p j := by
      intro i 
      specialize h₁ i
      rw [h₁]
      rw [Finset.sum_eq_sum_diff_singleton_add (show i ∈ Finset.univ by simp)]
      all_goals simp
      all_goals try tauto
    have eq3 : ∀ i, a i + p i = ∑ j : Fin 6, p j := h2
    have eq4 : ∑ i : Fin 6, (a i + p i) = ∑ i : Fin 6, (∑ j : Fin 6, p j) := by 
      apply Finset.sum_congr 
      . rfl 
      . intro i hi 
        exact eq3 i 
    simp at eq4 ⊢
    all_goals try tauto
    <;> try { tauto }
    all_goals try tauto
    have eq5 : ∑ i : Fin 6, (a i + p i) = ∑ i : Fin 6, a i + ∑ i : Fin 6, p i := by 
      simp [Finset.sum_add_distrib]
    have eq6 : ∑ i : Fin 6, (∑ j : Fin 6, p j) = 6 * ∑ j : Fin 6, p j := by 
      simp [Finset.sum_const, Finset.card_univ]
      all_goals try { try { tauto } }
      all_goals try { try { tauto } }
      all_goals try { try { tauto } }
    linarith [eq4, eq5, eq6]
  have h5 : ∑ i, (p i + a i + pa i) = 31 * (∑ i, p i) := by
    have eq3 : ∑ i, pa i = 5 * ∑ i, a i := eq1
    have eq4 : ∑ i, a i = 5 * ∑ i, p i := eq2
    have eq5 : ∑ i, pa i = 25 * (∑ i, p i) := by 
      linarith [eq3, eq4]
    calc 
      ∑ i, (p i + a i + pa i) = (∑ i, p i) + (∑ i, a i) + (∑ i, pa i) := by 
        simp [Finset.sum_add_distrib]
      _ = (∑ i, p i) + (5 * ∑ i, p i) + (25 * ∑ i, p i) := by 
        rw [eq4, eq5]
      _ = 31 * (∑ i, p i) := by 
        ring
  have h6 : 31 ∣ ∑ i, (p i + a i + pa i) := by 
    rw [h5]
    exact dvd_mul_right 31 (∑ i, p i)
  exact h6