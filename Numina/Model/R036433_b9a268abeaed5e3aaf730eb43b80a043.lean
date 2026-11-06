import Mathlib

open Real

theorem inequalities_264070 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (r : ℝ) (hr : r > 1) :
    (∑ i, (a i + b i) ^ r) ^ ((1 : ℝ) / r) ≤
    (∑ i, (a i) ^ r) ^ ((1 : ℝ) / r) +
    (∑ i, (b i) ^ r) ^ ((1 : ℝ) / r) := by
  have h_nonneg1 : ∀ i : Fin n, 0 ≤ a i := by 
    intro i 
    apply ha
  have h_nonneg2 : ∀ i : Fin n, 0 ≤ b i := by 
    intro i 
    apply hb
  have h2 : (∑ i, (a i + b i) ^ r) ^ ((1 : ℝ) / r) ≤
    (∑ i, (a i) ^ r) ^ ((1 : ℝ) / r) + (∑ i, (b i) ^ r) ^ ((1 : ℝ) / r) := by
    -- First, express the Minkowski inequality in terms of absolute values since we have non-negative terms.
    have h11 : (∑ i, (a i + b i) ^ r) ^ ((1 : ℝ) / r) =
        (∑ i, |a i + b i| ^ r) ^ ((1 : ℝ) / r) := by 
      congr 
      funext i 
      have h22 : 0 ≤ a i := h_nonneg1 i 
      have h33 : 0 ≤ b i := h_nonneg2 i 
      have h22' : 0 ≤ a i + b i := by linarith
      simp [abs_of_nonneg h22']
    have h12 : (∑ i, (a i) ^ r) ^ ((1 : ℝ) / r) =
        (∑ i, |a i| ^ r) ^ ((1 : ℝ) / r) := by 
      congr 
      funext i 
      have h22 : 0 ≤ a i := h_nonneg1 i 
      simp [abs_of_nonneg h22]
    have h13 : (∑ i, (b i) ^ r) ^ ((1 : ℝ) / r) =
        (∑ i, |b i| ^ r) ^ ((1 : ℝ) / r) := by 
      congr 
      funext i 
      have h22 : 0 ≤ b i := h_nonneg2 i 
      simp [abs_of_nonneg h22]
    have h16 : (∑ i, |a i + b i| ^ r) ^ ((1 : ℝ) / r) ≤ (∑ i, |a i| ^ r) ^ ((1 : ℝ) / r) + (∑ i, |b i| ^ r) ^ ((1 : ℝ) / r) := by
      have h10 : (∑ i, |a i + b i| ^ r) ^ ((1 : ℝ) / r) = ( (∑ i, |a i + b i| ^ r ) ) ^ ((1 : ℝ) / r ) := by rfl
      have hx1 : (∑ i, |a i| ^ r) ^ ((1 : ℝ) / r) = ( (∑ i, |a i| ^ r ) ) ^ ((1 : ℝ) / r ) := by rfl
      have hy1 : (∑ i, |b i| ^ r) ^ ((1 : ℝ) / r) = ( (∑ i, |b i| ^ r ) ) ^ ((1 : ℝ) / r ) := by rfl
      -- Now, apply the Lp_add_le theorem which is the triangle inequality for L^p norms.
      have h20 : (∑ i, |a i + b i| ^ r ) ^ ((1 : ℝ) / r) ≤ 
          (∑ i, |a i| ^ r ) ^ ((1 : ℝ) / r ) + (∑ i, |b i| ^ r ) ^ ((1 : ℝ) / r ) := by 
        apply Lp_add_le
        all_goals
          -- Note: The theorems in Mathlib involving Lp norms automatically handle
          -- the constraints like 1 ≤ p, etc from the context.
          -- Here, r > 1 satisfies 1 ≤ r for the Lp spaces (with the understanding that r is the p in Lp).
          simp_all [ha, hb, show r ≥ 1 by linarith]
          all_goals
            try {
              tauto
            }
            try {
              nlinarith
            }
        all_goals
          simp_all [ha, hb, show r ≥ 1 by linarith]
          all_goals
            try { 
              tauto 
            } 
            try { 
              nlinarith 
            }
      linarith 
    -- Combine these equalities and inequality to obtain the desired result.
    linarith [h11, h12, h13, h16]
  linarith