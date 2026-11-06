import Mathlib

open Real

theorem inequalities_186765 (n : ℕ) (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (h : ∑ i, (a i)^2 / b i ≤ ∑ i, b i) :
    ∑ i, a i ≤ ∑ i, b i := by

  have h11 : (∑ i : Fin n, a i) ^2 ≤ (∑ i : Fin n, b i) * (∑ i : Fin n, (a i) ^2 / b i) := by
    have h4 : ∀ i : Fin n, 0 < b i := by
      intro i
      apply hb
    have h5 : ∑ i : Fin n, (a i) ^2 / b i ≥ (∑ i : Fin n, (a i) ) ^2 / (∑ i : Fin n, (b i) ) := by 
      apply Finset.sq_sum_div_le_sum_sq_div
      intro i _
      specialize hb i
      linarith
    have h6 : 0 < (∑ i : Fin n, (b i) : ℝ) := by
      have h9 : ∀ i : Fin n, 0 < b i := hb
      have h11 : (∑ i : Fin n, (b i) : ℝ) > 0 := by
        apply Finset.sum_pos
        · -- All elements are positive
          intro i hi
          have h9i : 0 < b i := h9 i
          simpa using h9i
        · -- There exists at least one element in the sum
          use ⟨0, by omega⟩
          simp
      linarith
    have h7 : (∑ i : Fin n, (b i) : ℝ) * (∑ i : Fin n, (a i) ^2 / b i) ≥ (∑ i : Fin n, (a i) ) ^2 := by
      have h8 : (∑ i : Fin n, (a i) ^2 / b i) ≥ (∑ i : Fin n, (a i) ) ^2 / (∑ i : Fin n, (b i) ) := h5
      have h9 : 0 < (∑ i : Fin n, (b i) : ℝ) := h6
      have h10 : (∑ i : Fin n, (b i) : ℝ) * (∑ i : Fin n, (a i) ^2 / b i) ≥ (∑ i : Fin n, (b i) : ℝ) * ((∑ i : Fin n, (a i) ) ^2 / (∑ i : Fin n, (b i) ) ) := by 
        apply mul_le_mul_of_nonneg_left
        linarith [h8]
        all_goals 
          linarith [show 0 ≤ (∑ i : Fin n, (b i) : ℝ) by linarith]
      have h11 : (∑ i : Fin n, (b i) : ℝ) * ((∑ i : Fin n, (a i) ) ^2 / (∑ i : Fin n, (b i) ) ) = (∑ i : Fin n, (a i) ) ^2 := by 
        field_simp [show (∑ i : Fin n, (b i) : ℝ) ≠ 0 by linarith]
        <;> ring
      linarith [h10, h11, h6]
    linarith

  have h22 : (∑ i : Fin n, a i) ^2 ≤ (∑ i : Fin n, b i) ^2 := by
    have h33 : (∑ i : Fin n, (a i) ^2 / b i) ≤ (∑ i : Fin n, (b i) ) := by
      simpa using h
    nlinarith [h11, h33, show (∑ i : Fin n, (b i) : ℝ) > 0 by
      have h9 : ∀ i : Fin n, 0 < b i := hb
      have h11 : (∑ i : Fin n, (b i) : ℝ) > 0 := by 
        apply Finset.sum_pos
        · -- All elements are positive
          intro i hi
          have h9i : 0 < b i := h9 i
          simpa using h9i
        · -- There is at least one element
          use ⟨0, by omega⟩
          simp
      linarith
    ]
  have h33 : ∑ i : Fin n, (a i) ≥ 0 := by
    apply Finset.sum_nonneg
    intro i _
    specialize ha i
    linarith
  have h44 : ∑ i : Fin n, (b i) ≥ 0 := by
    apply Finset.sum_nonneg
    intro i _
    specialize hb i
    linarith
  nlinarith [h22, h33, h44]