import Mathlib

theorem algebra_100273 (x : Fin 10 → ℝ)
    (h₁ : ∑ i, |x i - 1| ≤ 4)
    (h₂ : ∑ i, |x i - 2| ≤ 6) :
    (∑ i, x i) / 10 = 1.4 := by
  have h3 : ∑ i : Fin 10, x i ≥ 6 := by
    have h17 : - (∑ i : Fin 10, (x i - 1)) ≤ 4 := by
      have h4 : ∀ i : Fin 10, - (x i - 1) ≤ |x i - 1| := by
        intro i
        cases' abs_cases (x i - 1) with h h <;> linarith
      have h5 : ∑ i : Fin 10, - (x i - 1) ≤ ∑ i : Fin 10, |x i - 1| := by
        apply Finset.sum_le_sum
        intro i hi
        specialize h4 i
        linarith
      simp at h5 ⊢
      nlinarith
    have h4 : ∑ i : Fin 10, (x i - 1) = ∑ i : Fin 10, x i - 10 := by
      simp [Finset.sum_sub_distrib]
      all_goals linarith
    nlinarith
  have h14 : ∑ i : Fin 10, x i ≤ 14 := by 
    have h15 : ∑ i : Fin 10, x i ≤ 14 := by
      have h16 : ∑ i : Fin 10, |x i - 1| = ∑ i : Fin 10, |x i - 1| := by rfl
      have h17 : ∑ i : Fin 10, |x i - 2| = ∑ i : Fin 10, |x i - 2| := by rfl
      have h18 : (∑ i : Fin 10, x i) - 10 ≤ 4 := by
        have h17 : ∑ i : Fin 10, (x i - 1) = (∑ i : Fin 10, x i) - 10 := by
          simp [Finset.sum_sub_distrib]
        have h18 : ∑ i : Fin 10, (x i - 1) ≤ ∑ i : Fin 10, |x i - 1| := by 
          apply Finset.sum_le_sum
          intro i hi
          have h22 : (x i - 1) ≤ |x i - 1| := by 
            cases' abs_cases (x i - 1) with h h <;> linarith 
          linarith
        nlinarith [h₁, h18, h17]
      have h19 : 14 - (∑ i : Fin 10, x i) ≤ 4 := by
        have h20 : ∑ i : Fin 10, (2 - x i) = 20 - (∑ i : Fin 10, x i) := by
          simp [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
          all_goals linarith
        have h21 : ∑ i : Fin 10, (2 - x i) ≤ ∑ i : Fin 10, |x i - 2| := by
          apply Finset.sum_le_sum
          intro i hi
          have h22 : (2 - x i) ≤ |x i - 2| := by 
            cases' abs_cases (x i - 2) with h h <;> linarith 
          linarith
        nlinarith [h₂, h21, h20]
      nlinarith
    linarith
  have h4 : (∑ i : Fin 10, x i) = 14 := by
    have h9 : (∑ i : Fin 10, x i) ≥ 14 := by
      have h20 : ∑ i : Fin 10, (2 - x i) = 20 - (∑ i : Fin 10, x i) := by
        simp [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
        all_goals linarith
      have h18 : ∑ i : Fin 10, (2 - x i) ≤ ∑ i : Fin 10, |x i - 2| := by
        apply Finset.sum_le_sum
        intro i hi
        have h6 : (2 - x i) ≤ |x i - 2| := by
          cases' abs_cases (x i - 2) with h h <;> linarith
        linarith
      -- From h₂: ∑ i : Fin 10, |x i - 2| ≤ 6 and from sum lemmas given, from (h)\∑i : Fin 10, x i <= 14
      have h21 : 20 - (∑ i : Fin 10, x i) ≤ 6 := by
        linarith [h18, h₂, h20]
      linarith
    have h9a : (∑ i : Fin 10, x i) ≤ 14 := by
      have h16a : (∑ i : Fin 10, (x i - 1)) = (∑ i : Fin 10, x i) - 10 := by
        simp [Finset.sum_sub_distrib]
        all_goals linarith
      have h17a : ∑ i : Fin 10, (x i - 1) ≤ ∑ i : Fin 10, |x i - 1| := by
        apply Finset.sum_le_sum
        intro i hi
        have h16b : (x i - 1) ≤ |x i - 1| := by
          cases' abs_cases (x i - 1) with h h <;> linarith
        linarith
      -- from hypothesis h₁: ∑ i : Fin 10, |x i - 1| ≤ 4
      have h16c : (∑ i : Fin 10, x i) - 10 ≤ 4 := by
        linarith [h₁, h17a, h16a]
      linarith
    linarith
  rw [h4]
  norm_num