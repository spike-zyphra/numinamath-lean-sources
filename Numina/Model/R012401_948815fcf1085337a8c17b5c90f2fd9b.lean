import Mathlib

open Real

theorem algebra_285837 {a : ℕ → ℝ} (ha : 1 = a 0)
    (hinc : ∀ n, a n ≤ a (n + 1)) (b : ℕ → ℝ)
    (hb : ∀ n, b n = ∑ k in Finset.Icc 1 n, ((1 - a (k - 1) / a k) * (1 / sqrt (a k))))
    (c : ℝ) (hc : 0 ≤ c) :
    ∀ n, 0 ≤ b n * c := by 
  intro n 
  have h1 : 0 ≤ b n := by 
    rw [hb n]
    have h2 : ∀ k, k ∈ Finset.Icc 1 n → 0 ≤ (1 - a (k - 1) / a k) * (1 / sqrt (a k)) := by 
      intro k hk 
      have h3 : 1 ≤ k := by 
        have h4 : k ∈ Finset.Icc 1 n := hk
        simp at h4 ⊢ 
        linarith 
      have h5 : a k ≥ a (k - 1) := by 
        have h6 : k - 1 ≤ k := by omega 
        have h7 : (k - 1 : ℕ) ≤ (k : ℕ) := by omega 
        specialize hinc (k - 1) 
        have h8 : a (k - 1) ≤ a ((k - 1) + 1) := hinc 
        have h9 : (k - 1 + 1 : ℕ) = k := by 
          omega 
        rw [show (k - 1 + 1 : ℕ) = k by omega] at h8 
        linarith 
      have h7 : ∀ m, a m ≥ 1 := by 
        intro m 
        induction m with 
        | zero => 
          rw [show a 0 = 1 by linarith [ha]]
          all_goals norm_num 
        | succ m ih => 
          have h11 : a (m + 1) ≥ a m := by 
            specialize hinc m
            simpa using hinc 
          have h12 : a m ≥ 1 := ih 
          linarith 
      have h6 : a k ≥ 1 := h7 k 
      have h9 : a (k - 1) ≥ 1 := by 
        have h7' : ∀ m, a m ≥ 1 := h7 
        specialize h7' (k - 1) 
        linarith 
      have h10 : 0 ≤ 1 - a (k - 1) / a k := by 
        have h11 : a k ≥ a (k - 1) := h5 
        have h12 : a k > 0 := by 
          linarith 
        have h13 : a (k - 1) / a k ≤ (a k) / (a k) := by 
          apply (div_le_div_right h12).mpr 
          linarith 
        have h14 : (a k) / (a k) = 1 := by 
          have h15 : a k > 0 := by 
            linarith 
          field_simp [h15] 
        linarith [h13, h14] 
      have h12 : 0 ≤ (1 / sqrt (a k)) := by 
        have h13 : a k ≥ 1 := h6 
        have h14 : sqrt (a k) ≥ 0 := Real.sqrt_nonneg (a k) 
        have h15 : sqrt (a k) > 0 := by 
          apply Real.sqrt_pos.mpr 
          linarith 
        positivity 
      positivity 
    apply Finset.sum_nonneg 
    intro i hi 
    specialize h2 i hi 
    simpa using h2 
  have h12 : 0 ≤ b n * c := by 
    apply mul_nonneg 
    all_goals linarith [h1, hc] 
  linarith