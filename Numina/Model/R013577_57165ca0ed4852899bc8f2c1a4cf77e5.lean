import Mathlib

theorem algebra_230782 (k m : Fin 7 → ℕ) (h₀ : ∀ i, k i = ∑ j in Finset.univ \ {i}, m j)
    (h₁ : ∑ i, k i = 2022) :
    ∑ i, m i = 337 := by
  have h2 : ∀ i : Fin 7, k i + m i = ∑ j : Fin 7, m j := by
    intro i
    have h3 : k i = ∑ j in Finset.univ \ {i}, m j := h₀ i
    rw [h3]
    rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i)]
    all_goals try { omega }
    all_goals try { tauto }
    all_goals try { linarith }
    all_goals try { tauto }
  have eq1 : ∑ i : Fin 7, (k i + m i) = 7 * (∑ j : Fin 7, m j) := by
    calc
      ∑ i : Fin 7, (k i + m i) = ∑ i : Fin 7, (∑ j : Fin 7, m j) := by 
        congr 
        funext i
        exact h2 i 
      _ = 7 * (∑ j : Fin 7, m j) := by 
        simp [Finset.sum_const, Finset.card_univ]
        <;> try { ring }
  have eq2 : ∑ i : Fin 7, (k i + m i) = (∑ i : Fin 7, k i) + (∑ i : Fin 7, m i) := by 
    simp [Finset.sum_add_distrib]
  have eq3 : (∑ i : Fin 7, k i) + (∑ i : Fin 7, m i) = 7 * (∑ j : Fin 7, m j) := by 
    calc 
      (∑ i : Fin 7, k i) + (∑ i : Fin 7, m i) = ∑ i : Fin 7, (k i + m i) := by 
        rw [Finset.sum_add_distrib]
      _ = 7 * (∑ j : Fin 7, m j) := eq1
  rw [h₁] at eq3
  have h3 : (∑ i : Fin 7, m i) = 337 := by
    omega 
  exact h3
  all_goals try { tauto }
  all_goals try { omega }
  all_goals try { tauto }
  all_goals try { omega }
  all_goals try { tauto }
  all_goals try { omega }
  all_goals try { tauto }