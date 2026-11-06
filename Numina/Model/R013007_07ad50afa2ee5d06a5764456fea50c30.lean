import Mathlib

open Real

theorem inequalities_270049 (a : ℕ → ℝ) (ha : 1 = a 0)
    (hinc : ∀ n, a n ≤ a (n + 1)) (b : ℕ → ℝ)
    (hb : ∀ n, b n = ∑ k in Finset.Icc 1 n, ((1 - a (k - 1) / a k) / sqrt (a k))) :
    ∀ n, 0 < n → 0 ≤ b n := by
  intro n hn
  rw [hb n]
  have h2 : ∀ k : ℕ, k ∈ Finset.Icc 1 n → 0 ≤ (1 - a (k - 1) / a k) / sqrt (a k) := by
    intro k hk
    have h3 : 1 ≤ k := by
      have h3 : k ∈ Finset.Icc 1 n := hk
      simp at h3 ⊢
      omega
    have h4 : k ≤ n := by
      have h4 : k ∈ Finset.Icc 1 n := hk
      simp at h4 ⊢
      omega
    have h7 : 0 < a k := by
      have h14 : ∀ (i : ℕ), a 0 ≤ a i := by
        intro i
        induction i with
        | zero =>
          simp [ha]
        | succ i ih =>
          have h12 : a i ≤ a (i + 1) := hinc i
          linarith [h12, ih]
      have h15 : a 0 = 1 := by linarith
      have h16 : a k ≥ 1 := by
        specialize h14 k
        nlinarith [h14, h15]
      linarith
    have h9 : 0 < sqrt (a k) := by
      apply Real.sqrt_pos.2
      linarith [h7]
    have h10 : 0 ≤ (1 - a (k - 1) / a k) := by
      have h12 : a (k - 1) ≤ a k := by
        by_cases h : k - 1 ≤ k
        · -- The index is in bounds, so apply hinc
          have h11 : a (k - 1) ≤ a (k - 1 + 1) := by
            apply hinc (k - 1)
          have h12 : k - 1 + 1 = k := by omega
          rw [h12] at h11
          linarith
        · -- k - 1 > k, which is not possible
          omega
      have h11 : a k > 0 := by linarith [h7]
      have h13 : 0 ≤ 1 - a (k - 1) / a k := by
        have h14 : a k - a (k - 1) ≥ 0 := by linarith [h12]
        have h15 : a k > 0 := h11
        have h16 : (1 - a (k - 1) / a k) = (a k - a (k - 1)) / a k := by
          field_simp [h15]
          <;> ring
        rw [h16]
        apply div_nonneg
        · linarith
        · linarith
      linarith
    apply div_nonneg
    · linarith [h10]
    · -- Show sqrt(a k) ≥ 0
      positivity
  apply Finset.sum_nonneg (h2)