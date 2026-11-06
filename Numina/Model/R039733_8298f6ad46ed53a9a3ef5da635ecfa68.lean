import Mathlib

open Real

theorem inequalities_127664 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    ∑ i, (a i)^2 / b i ≥ (∑ i, a i)^2 / ∑ i, b i := by 
  have h2 : ∑ i, b i > 0 := by 
    apply Finset.sum_pos 
    intro i hi 
    exact hb i 
    use ⟨0, by linarith⟩ 
    simp
  have h3 : (∑ i : Fin n, a i) ^ 2 ≤ (∑ i, (a i) ^ 2 / b i) * (∑ i, b i) := by 
    have h4 : ∀ i : Fin n, b i > 0 := hb 
    have h5 : ∀ i : Fin n, a i > 0 := by
      intro i 
      exact ha i
    have h6 : (∑ i : Fin n, (a i / Real.sqrt (b i)) * Real.sqrt (b i)) ^ 2 ≤ (∑ i : Fin n, (a i / Real.sqrt (b i) ) ^ 2) * (∑ i : Fin n, (Real.sqrt (b i)) ^ 2) := by 
      apply Finset.sum_mul_sq_le_sq_mul_sq
    have h7 : ∑ i : Fin n, (a i / Real.sqrt (b i)) * Real.sqrt (b i) = ∑ i : Fin n, a i := by 
      apply Finset.sum_congr 
      · rfl 
      · intro i hi
        have h8 : Real.sqrt (b i) > 0 := by 
          apply Real.sqrt_pos.mpr 
          linarith [hb i]
        field_simp [h8]
    have h8 : ∑ i : Fin n, (a i / Real.sqrt (b i) ) ^ 2 = ∑ i : Fin n, (a i) ^ 2 / b i := by
      apply Finset.sum_congr
      · rfl 
      · intro i hi 
        have h9 : b i > 0 := hb i 
        have h10 : Real.sqrt (b i) > 0 := by 
          apply Real.sqrt_pos.mpr 
          linarith 
        have h11 : (a i / Real.sqrt (b i)) ^ 2 = (a i) ^ 2 / b i := by
          have h12 : Real.sqrt (b i) > 0 := h10 
          have h13 : (Real.sqrt (b i)) ^ 2 = b i := Real.sq_sqrt (by linarith)
          field_simp [h12, show b i ≠ 0 by linarith]
          <;> nlinarith [Real.sqrt_nonneg (b i), sq_nonneg (a i)]
        linarith [h11]
    have h9 : ∑ i : Fin n, (Real.sqrt (b i)) ^ 2 = ∑ i : Fin n, b i := by 
      apply Finset.sum_congr 
      · rfl 
      · intro i hi
        have h10 : b i > 0 := hb i 
        have h11 : (Real.sqrt (b i)) ^ 2 = b i := Real.sq_sqrt (by linarith)
        simp [h11]
    rw [h7, h8, h9] at h6 
    linarith 
  have h12 : ∑ i, (a i)^2 / b i ≥ (∑ i, a i)^2 / ∑ i, b i := by 
    have h2' : ∑ i, b i > 0 := h2 
    have h13 : (∑ i : Fin n, a i) ^ 2 ≤ (∑ i, (a i) ^ 2 / b i) * (∑ i, b i) := h3 
    have h14 : (∑ i : Fin n, (a i) ^ 2 / b i) ≥ (∑ i : Fin n, a i) ^ 2 / (∑ i, b i) := by 
      apply (div_le_iff₀ (by linarith)).mpr 
      nlinarith 
    linarith 
  exact h12