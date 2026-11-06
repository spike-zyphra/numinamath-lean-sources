import Mathlib

open Real

theorem inequalities_135810 (n : ℕ) (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    ∑ i, (a i)^2 / b i ≥ (∑ i, a i)^2 / ∑ i, b i := by
  have h1 : 0 < ∑ i, b i := by
    apply Finset.sum_pos 
    intro i hi 
    exact hb i 
    use ⟨0, by omega⟩ 
    simp 
  have h3 : ∑ i : Fin n, ((a i) ^ 2 / (b i)) ≥ (∑ i : Fin n, (a i)) ^ 2 / (∑ i : Fin n, b i) := by
    have h4 : ∀ i : Fin n, 0 < b i := hb 
    have h5 : (∑ i : Fin n, (a i) ^ 2 / (b i)) ≥ (∑ i : Fin n, (a i)) ^ 2 / (∑ i : Fin n, b i) := by
      have h6 : 0 < ∑ i : Fin n, b i := h1 
      have h7 : (∑ i : Fin n, (a i) ^ 2 / (b i)) * (∑ i : Fin n, b i) ≥ (∑ i : Fin n, a i) ^ 2 := by 
        have h14 : ∀ i : Fin n, 0 < b i := hb 
        have h9 : (∑ i : Fin n, (a i / Real.sqrt (b i)) * Real.sqrt (b i)) ^ 2 ≤ (∑ i : Fin n, (a i / Real.sqrt (b i)) ^ 2) * (∑ i : Fin n, (Real.sqrt (b i)) ^ 2) := by 
          apply Finset.sum_mul_sq_le_sq_mul_sq
        have h9' : ∑ i : Fin n, (a i / Real.sqrt (b i)) * Real.sqrt (b i) = ∑ i : Fin n, a i := by 
          apply Finset.sum_congr 
          · rfl 
          intro i hi 
          have hb' : 0 < b i := hb i 
          have h16 : 0 < Real.sqrt (b i) := by apply Real.sqrt_pos.mpr; exact hb' 
          field_simp [Real.sq_sqrt (show 0 ≤ b i by linarith)]
        have h10' : ∑ i : Fin n, (a i / Real.sqrt (b i)) ^ 2 = ∑ i : Fin n, (a i) ^ 2 / (b i) := by 
          apply Finset.sum_congr 
          · rfl 
          intro i hi 
          have hb' : 0 < b i := hb i 
          have h16 : 0 < Real.sqrt (b i) := by apply Real.sqrt_pos.mpr; exact hb' 
          field_simp [Real.sq_sqrt (show 0 ≤ b i by linarith)]
        have h11' : ∑ i : Fin n, (Real.sqrt (b i)) ^ 2 = ∑ i : Fin n, b i := by 
          apply Finset.sum_congr 
          · rfl 
          intro i hi 
          have hb' : 0 < b i := hb i 
          have h16 : 0 < Real.sqrt (b i) := by apply Real.sqrt_pos.mpr; exact hb' 
          rw [Real.sq_sqrt]
          all_goals linarith
        rw [h9', h10', h11'] at h9 
        have h12 : (∑ i : Fin n, (a i) ^ 2 / (b i)) * (∑ i : Fin n, b i) ≥ (∑ i : Fin n, a i) ^ 2 := by
          nlinarith 
        nlinarith 
      have h17 : (∑ i : Fin n, (a i) ^ 2 / (b i)) * (∑ i : Fin n, b i) ≥ (∑ i : Fin n, a i) ^ 2 := h7 
      have h12 : (∑ i : Fin n, b i) > 0 := h1 
      have h13 : ∑ i : Fin n, ((a i) ^ 2 / (b i)) ≥ (∑ i : Fin n, a i) ^ 2 / (∑ i : Fin n, b i) := by 
        apply (div_le_iff₀ (by linarith)).mpr 
        nlinarith 
      linarith 
    linarith
  linarith [h3]