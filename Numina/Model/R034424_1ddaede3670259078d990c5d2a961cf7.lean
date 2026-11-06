import Mathlib

theorem inequalities_70784 (n : ℕ) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 10) (hsumsq : ∑ i, (a i)^2 > 20) :
    ∑ i, (a i)^3 > 40 := by
  have h1 : (∑ i, (a i) ^ 2) ^ 2 ≤ (∑ i, a i) * (∑ i, (a i) ^ 3) := by
    have h1 : (∑ i : Fin n, ((√(a i)) : ℝ) * ((√(a i) * (a i)) : ℝ)) ^ 2 ≤ (∑ i : Fin n, ((√(a i)) : ℝ) ^ 2) * (∑ i : Fin n, ((√(a i) * (a i)) : ℝ) ^ 2) := by
      apply Finset.sum_mul_sq_le_sq_mul_sq
    have h7 : (∑ i : Fin n, ((√(a i)) : ℝ) * ((√(a i) * (a i)) : ℝ)) = (∑ i, (a i) ^ 2) := by
      have h9 : ∀ i : Fin n, ((√(a i)) : ℝ) * ((√(a i) * (a i)) : ℝ) = (a i) ^ 2 := by
        intro i
        have ha5 : 0 ≤ a i := by
          have h4 : 0 < a i := ha i
          linarith
        have h9 : ((√(a i)) : ℝ) * ((√(a i) * (a i)) : ℝ) = (a i) ^ 2 := by
          calc
            ((√(a i)) : ℝ) * ((√(a i) * (a i)) : ℝ) = (√(a i) * √(a i)) * (a i) := by ring
            _ = (a i) * (a i) := by
              have h10 : (√(a i) * √(a i)) = (a i) := by
                rw [Real.mul_self_sqrt]
                linarith
              rw [h10]
            _ = (a i) ^ 2 := by ring
        linarith
      calc
        (∑ i : Fin n, ((√(a i)) : ℝ) * ((√(a i) * (a i)) : ℝ))
          = (∑ i : Fin n, ((√(a i) * (√(a i) * (a i)) ) ) ) := by rfl
        _ = (∑ i : Fin n, (a i) ^ 2) := by
          apply Finset.sum_congr
          . rfl
          intro i _
          specialize h9 i
          linarith
        _ = (∑ i, (a i) ^ 2) := by rfl
    have h2 : (∑ i : Fin n, ((√(a i)) : ℝ) ^ 2) = (∑ i, a i) := by
      have h3 : ∀ i : Fin n, ((√(a i)) : ℝ) ^ 2 = (a i) := by
        intro i
        have h4 : 0 < a i := ha i
        have h5 : 0 ≤ a i := by linarith
        have h7 : ((√(a i)) : ℝ) ^ 2 = (a i) := Real.sq_sqrt (show 0 ≤ a i by linarith)
        linarith
      calc
        (∑ i : Fin n, ((√(a i)) : ℝ) ^ 2) = (∑ i : Fin n, (a i : ℝ)) := by
          apply Finset.sum_congr
          . rfl
          intro i _
          specialize h3 i
          linarith
        _ = (∑ i, a i) := by rfl
    have h3 : (∑ i : Fin n, ((√(a i) * (a i)) : ℝ) ^ 2) = (∑ i, (a i) ^ 3) := by
      have h4 : ∀ i : Fin n, ((√(a i) * (a i)) : ℝ) ^ 2 = (a i) ^ 3 := by
        intro i
        have h9 : 0 ≤ a i := by
          have h4 : 0 < a i := ha i
          linarith
        have h5 : ((√(a i) * (a i)) : ℝ) ^ 2 = (a i) ^ 3 := by
          calc
            ((√(a i) * (a i)) : ℝ) ^ 2 = (√(a i) ^ 2) * (a i) ^ 2 := by ring
            _ = (a i) * (a i) ^ 2 := by
              have h7 : (√(a i) ^ 2) = (a i) := by
                rw [Real.sq_sqrt]
                linarith
              rw [h7]
            _ = (a i) ^ 3 := by ring
        linarith
      calc
        (∑ i : Fin n, ((√(a i) * (a i)) : ℝ) ^ 2) = (∑ i : Fin n, (a i) ^ 3) := by
          apply Finset.sum_congr
          . rfl
          intro i _
          specialize h4 i
          linarith
        _ = (∑ i, (a i) ^ 3) := by rfl
    rw [h7, h2, h3] at h1
    linarith
  have h2 : (∑ i, (a i) ^ 3) ≥ (∑ i, (a i) ^ 2) ^ 2 / (∑ i, a i) := by
    have h3 : (∑ i, (a i) ^ 2) ^ 2 ≤ (∑ i, a i) * (∑ i, (a i) ^ 3) := h1
    have h4 : (∑ i, a i) > 0 := by
      have h5 : (∑ i, a i) = 10 := hsum
      linarith
    have h22 : (∑ i, (a i) ^ 3) ≥ (∑ i, (a i) ^ 2) ^ 2 / (∑ i, a i) := by
      apply (div_le_iff₀ (by linarith)).mpr
      linarith
    linarith
  have h3 : (∑ i, (a i) ^ 2) ^ 2 > 400 := by
    have h14 : (∑ i, (a i) ^ 2) > 20 := hsumsq
    nlinarith [sq_nonneg ((∑ i, (a i) ^ 2) - 20)]
  have h5 : (∑ i, (a i) ^ 2) ^ 2 / (∑ i, a i) > 40 := by
    have h7 : (∑ i, (a i) ^ 2) ^ 2 > 400 := h3
    have h8 : (∑ i, a i) = 10 := hsum
    rw [h8] at *
    apply (lt_div_iff₀ (by norm_num)).mpr
    all_goals nlinarith
  linarith [h2, h5]