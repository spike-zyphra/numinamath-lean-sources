import Mathlib

theorem algebra_263077 (a : Fin 16 → ℝ) (ha : ∑ i, a i = 100) (hb : ∑ i, (a i)^2 = 1000) :
    a 15 ≤ 25 := by
  have h1 : ∑ i : Fin 16, a i = 100 := ha
  have h2 : ∑ i : Fin 16, (a i)^2 = 1000 := hb

  have h3 : a 15 ≤ 25 := by
    have h4 : (∑ i in Finset.range 15, a i) + a 15 = 100 := by
      have h5 : ∑ i in Finset.range 16, a i = (∑ i in Finset.range 15, a i) + a 15 := by
        simp [Finset.sum_range_succ]
      have h6 : ∑ i in Finset.range 16, a i = 100 := by
        simpa using h1
      linarith [h5, h6]

    have h7 : (∑ i in Finset.range 15, (a i)^2) + (a 15) ^ 2 = 1000 := by
      have h8 : ∑ i in Finset.range 16, (a i : ℝ)^2 = (∑ i in Finset.range 15, (a i)^2) + (a 15) ^ 2 := by 
        simp [Finset.sum_range_succ]
      have h9 : ∑ i in Finset.range 16, (a i : ℝ)^2 = 1000 := by 
        simpa using h2
      linarith [h8, h9]

    have h8 : (∑ i in Finset.range 15, (a i)^2) ≥ ((∑ i in Finset.range 15, a i) )^2 / 15 := by
      have h9 : ( ∑ i in Finset.range 15, a i ) ^ 2 ≤ (15 : ℝ) * ∑ i in Finset.range 15, (a i : ℝ) ^ 2 := by 
        have h10 : ( ∑ i in Finset.range 15, a i ) ^ 2 = ( ∑ i in Finset.range 15, (a i : ℝ) * (1 : ℝ) ) ^ 2 := by 
          simp 
        have h11 : ( ∑ i in Finset.range 15, (a i : ℝ) * (1 : ℝ) ) ^ 2 ≤ ( ∑ i in Finset.range 15, (a i : ℝ) ^ 2 ) * ( ∑ i in Finset.range 15, (1 : ℝ) ^ 2 ) := by 
          apply Finset.sum_mul_sq_le_sq_mul_sq 
        have h12 : ∑ i in Finset.range 15, (1 : ℝ) ^ 2 = (15 : ℝ) := by 
          simp 
        rw [h10] 
        rw [h12] at h11 
        nlinarith 
      have h13 : ( ∑ i in Finset.range 15, (a i ) ^2 ) = ( ∑ i in Finset.range 15, (a i ) ^2 ) := by 
        rfl 
      have h14 : ( ∑ i in Finset.range 15, a i ) ^ 2 ≤ (15 : ℝ) * ( ∑ i in Finset.range 15, (a i ) ^2 ) := h9 
      have h15 : ( ∑ i in Finset.range 15, (a i ) ^2 ) ≥ ( ( ∑ i in Finset.range 15, a i ) ^2 ) / (15 : ℝ) := by 
        nlinarith 
      linarith

    have h10 : (∑ i in Finset.range 15, a i) = 100 - a 15 := by 
      linarith [h4]

    have h11 : (∑ i in Finset.range 15, (a i)^2) = 1000 - (a 15) ^ 2 := by 
      nlinarith

    rw [h10] at h8 
    rw [h11] at h8 
    have h12 : 15 * (1000 - (a 15) ^ 2) ≥ (100 - a 15) ^ 2 := by
      nlinarith 
    nlinarith [sq_nonneg (a 15 - 25), sq_nonneg (a 15 + 25 / 4)]
  linarith