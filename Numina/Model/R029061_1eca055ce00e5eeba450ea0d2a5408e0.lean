import Mathlib

theorem algebra_303566 {k : ℤ} (hk : ∃ x1 x2 : ℤ, x1 ≠ x2 ∧ k * x1 ^ 2 + (k + 1) * x1 + (k - 1) = 0 ∧ k * x2 ^ 2 + (k + 1) * x2 + (k - 1) = 0) :
    k = 1 := by
  rcases hk with ⟨x1, x2, hx1x2, h1, h2⟩
  have h3 : k * (x1 + x2 + 1) = -1 := by
    have h4 : k * (x1 ^ 2 - x2 ^ 2) + (k + 1) * (x1 - x2) = 0 := by
      nlinarith 
    have h5 : k * (x1 + x2) * (x1 - x2) + (k + 1) * (x1 - x2) = 0 := by
      ring_nf at h4 ⊢
      nlinarith 
    have h6 : (x1 - x2) * (k * (x1 + x2) + k + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Assume h7: x1 - x2 = 0
      exfalso
      apply hx1x2
      have : x1 = x2 := by linarith 
      assumption 
    · -- Assume h8: k * (x1 + x2) + k + 1 = 0
      nlinarith 
  have h5 : k ∣ -1 := by
    use (x1 + x2 + 1)
    linarith 
  have h5' : k ∣ 1 := by
    exact Int.dvd_neg.mp h5
  have : k = 1 ∨ k = -1 := by
    have h6 : k ≤ 1 := by
      apply Int.le_of_dvd (by norm_num) h5'
    have h7 : -1 ≤ k := by
      have h8 : k ∣ 1 := h5'
      have h9 : -k ∣ 1 := by 
        exact Int.neg_dvd.2 h8
      have h10 : -k ≤ 1 := by 
        apply Int.le_of_dvd (by norm_num) h9 
      omega 
    interval_cases k <;> try { tauto }
  cases' this with h11 h11
  · -- Assume k = 1
    exact h11 
  · -- Assume k = -1
    exfalso 
    rw [h11] at h1 h2 
    nlinarith [sq_nonneg x1, sq_nonneg x2]