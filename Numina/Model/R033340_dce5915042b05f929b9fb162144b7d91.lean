import Mathlib

open Real
open scoped BigOperators

theorem inequalities_175182 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
  (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
  (h : ∑ i, a i = ∑ i, b i) :
  1 / 2 * ∑ i, a i ≤ ∑ i, (a i)^2 / (a i + b i) := by

  have h1 : ∀ i, 0 < a i + b i := by
    intro i 
    have ha2 : 0 < a i := ha i 
    have hb2 : 0 < b i := hb i 
    linarith

  have h_eq : ∑ i, (a i + b i) = 2 * (∑ i, a i) := by 
    calc 
      ∑ i, (a i + b i) = ∑ i, (a i) + ∑ i, (b i) := by 
        simp [Finset.sum_add_distrib]
      _ = (∑ i, a i) + (∑ i, a i) := by 
        rw [show ∑ i, (b i) = ∑ i, (a i) by 
          rw [h]
        ]
      _ = 2 * (∑ i, a i) := by 
        ring

  have h5 : ∑ i, (a i)^2 / (a i + b i) ≥ (∑ i, a i) ^ 2 / (∑ i, (a i + b i)) := by
    have h6 : ∀ i, 0 < a i + b i := by 
      intro i 
      specialize ha i 
      specialize hb i 
      linarith 
    apply Finset.sq_sum_div_le_sum_sq_div 
    intro i hi 
    have ha2 : 0 < a i := ha i 
    have hb2 : 0 < b i := hb i 
    have h10 : 0 < a i + b i := by 
      linarith [ha2, hb2] 
    exact h10

  have h5' : (∑ i, a i) ^ 2 / (∑ i, (a i + b i)) = (∑ i, a i) / 2 := by 
    rw [h_eq]
    have h3 : ∑ i : Fin n, a i > 0 := by 
      have h4 : ∀ i, 0 < a i := ha 
      have hn2 : n > 0 := hn 
      have h7 : ∑ i : Fin n, a i > 0 := by 
        apply Finset.sum_pos 
        intro i hi 
        exact h4 i 
        use ⟨0, by omega⟩ 
        simp 
      linarith 
    have h5'1 : ((∑ i : Fin n, a i) ^ 2) / (2 * (∑ i : Fin n, a i) ) = (∑ i : Fin n, a i) / 2 := by
      have h31 : ∑ i : Fin n, a i > 0 := h3 
      field_simp [h31] 
      <;> ring 
    exact h5'1 

  have h6 : ∑ i, (a i) ^ 2 / (a i + b i) ≥ (∑ i, a i) / 2 := by 
    linarith [h5, h5']

  linarith [h6]