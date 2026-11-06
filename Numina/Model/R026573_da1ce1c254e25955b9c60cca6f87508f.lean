import Mathlib

open Real

theorem algebra_213482 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (h : ∃ x, ∀ i, a i / b i = x) :
    ∑ i, sqrt (a i * b i) =
    sqrt (∑ i, a i) * sqrt (∑ i, b i) := by

  rcases h with ⟨x, hx⟩
  have hx1 : ∀ i, a i = x * b i := by
    intro i
    have h1 : b i ≠ 0 := by linarith [hb i]
    have h2 : a i / b i = x := hx i
    field_simp at h2 ⊢
    <;> linarith

  have hsum1 : ∑ i, a i = x * ∑ i, b i := by
    calc 
      ∑ i, a i = ∑ i, (x * b i) := by 
        congr 
        funext i 
        exact hx1 i 
      _ = x * ∑ i, b i := by 
        rw [Finset.mul_sum]

  have hx8 : x ≥ 0 := by
    by_contra h
    push_neg at h
    have h9 : x < 0 := h
    have h10 := ha ⟨0, by linarith⟩
    have h11 := hb ⟨0, by linarith⟩
    have hx2 := hx1 ⟨0, by linarith⟩
    have hx2' : x * (b ⟨0, by linarith⟩) = a ⟨0, by linarith⟩ := by linarith
    have hbi_pos : b ⟨0, by linarith⟩ > 0 := h11
    have ha_pos : a ⟨0, by linarith⟩ > 0 := h10 
    have hx3 : x * (b ⟨0, by linarith⟩) > 0 := by 
      nlinarith
    nlinarith

  have h1 : ∀ i : Fin n, sqrt (a i * b i) = Real.sqrt x * (b i) := by 
    intro i 
    have h2 : a i * b i = x * (b i) ^ 2 := by
      rw [show a i = x * b i by linarith [hx1 i]]
      all_goals 
        nlinarith 
    have h3 : 0 ≤ b i := by linarith [hb i]
    have h4 : sqrt (a i * b i) = sqrt (x * (b i) ^ 2) := by 
      rw [h2]
    have h9 : sqrt (x * (b i) ^ 2) = Real.sqrt x * (b i) := by 
      calc 
        sqrt (x * (b i) ^ 2) = sqrt (x * ((b i) ^ 2)) := by ring_nf 
        _ = sqrt x * sqrt ((b i) ^ 2) := by 
          rw [Real.sqrt_mul (by 
            have hx2 : x ≥ 0 := hx8 
            have hbi2 : (b i) ^ 2 ≥ 0 := by positivity 
            nlinarith 
          )]
        _ = sqrt x * (b i) := by 
          have h10 : sqrt ((b i) ^ 2) = b i := by 
            rw [Real.sqrt_sq (by 
              linarith [hb i]
            )]
          rw [h10]
    rw [h4, h9]

  have h2 : ∑ i, sqrt (a i * b i) = Real.sqrt x * (∑ i, b i) := by 
    calc 
      ∑ i, sqrt (a i * b i) = ∑ i, (Real.sqrt x * (b i)) := by 
        congr 
        funext i 
        exact h1 i 
      _ = Real.sqrt x * (∑ i, b i) := by 
        rw [Finset.mul_sum]

  -- Now prove the right side is equal
  have hsum2 : ∑ i, a i ≥ 0 := by
    apply Finset.sum_nonneg 
    intro i hi 
    have ha2 := ha i 
    linarith

  have hsum3 : ∑ i, b i ≥ 0 := by
    apply Finset.sum_nonneg 
    intro i hi 
    have hb2 := hb i 
    linarith

  have h2' : sqrt (∑ i, a i) * sqrt (∑ i, b i) = Real.sqrt x * (∑ i, b i) := by
    have h3 : sqrt (∑ i, a i) * sqrt (∑ i, b i) = sqrt ((∑ i, a i) * (∑ i, b i)) := by 
      calc 
        sqrt (∑ i, a i) * sqrt (∑ i, b i) = sqrt ((∑ i, a i) * (∑ i, b i)) := by 
          rw [← Real.sqrt_mul (by 
            have h4 : (∑ i, a i) ≥ 0 := hsum2 
            have h5 : (∑ i, b i) ≥ 0 := hsum3 
            nlinarith 
          )]
        _ = sqrt ((∑ i, a i) * (∑ i, b i)) := by rfl
    have h3' : (∑ i, a i) * (∑ i, b i) = x * ((∑ i, b i) ^ 2) := by 
      calc 
        (∑ i, a i) * (∑ i, b i) = (x * ∑ i, b i) * (∑ i, b i) := by 
          rw [hsum1]
        _ = x * ((∑ i, b i) ^ 2) := by 
          ring 
    rw [h3, h3']
    have h6 : sqrt (x * ((∑ i, b i) ^ 2)) = (∑ i, b i) * Real.sqrt x := by 
      have h7 : x * ((∑ i, b i) ^ 2) = ( (∑ i, b i) ^ 2) * x := by 
        ring 
      rw [h7]
      have h8 : (∑ i, b i) ^ 2 ≥ 0 := by 
        positivity 
      have h9 : sqrt (( (∑ i, b i) ^ 2) * x) = (∑ i, b i) * Real.sqrt x := by 
        rw [Real.sqrt_mul (by 
          have hsum3' : (∑ i, b i) ^ 2 ≥ 0 := by positivity 
          have hx8' : x ≥ 0 := hx8 
          nlinarith
        )]
        have h10 : sqrt ((∑ i, b i) ^ 2) = (∑ i, b i) := by 
          rw [Real.sqrt_sq (by 
            nlinarith 
          )]
        rw [h10]
        <;> nlinarith 
      linarith [h9]
    rw [h6]
    <;> ring_nf <;> nlinarith

  linarith [h2, h2']