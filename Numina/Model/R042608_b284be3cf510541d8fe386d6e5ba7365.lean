import Mathlib

open Finset Real

theorem inequalities_603962 (p n : ℕ) (hp : 0 < p) (hn : 0 < n)
    (C : ℕ → ℕ → ℝ) (hC : ∀ h ∈ Icc 1 n, ∀ k ∈ Icc 1 (p * h), C h k ∈ Set.Icc 0 1) :
    ∑ h ∈ Icc 1 n, ∑ k ∈ Icc 1 (p * h), ((C h k) / h) ^ 2 ≤
    2 * p * ∑ h ∈ Icc 1 n, ∑ k ∈ Icc 1 (p * h), C h k := by
  have h1 : ∀ h : ℕ, h ∈ Icc 1 n → ∀ k : ℕ, k ∈ Icc 1 (p * h) → ((C h k) / h) ^ 2 ≤ 2 * p * (C h k) := by
    intro h hh k hk
    have hh1 : 1 ≤ h := by 
      have h2 : h ≥ 1 := by 
        have h3 : h ∈ Icc 1 n := hh
        simp at h3 ⊢
        omega
      omega
    have hk1 : 1 ≤ k := by 
      have k2 : k ≥ 1 := by 
        have k3 : k ∈ Icc 1 (p * h) := hk
        simp at k3 ⊢
        omega
      omega
    have h2 : 0 ≤ C h k := by
      have h3 : C h k ∈ Set.Icc (0 : ℝ) (1 : ℝ) := hC h hh k hk
      simp at h3 ⊢
      linarith [h3.1, h3.2]
    have h3 : (C h k) ^ 2 ≤ 2 * p * (C h k) * (h ^ 2 : ℝ) := by
      have h4 : (C h k) ≥ 0 := by
        have h3 : C h k ∈ Set.Icc (0 : ℝ) (1 : ℝ) := hC h hh k hk
        simp at h3 ⊢
        linarith [h3.1, h3.2]
      have h5 : (C h k) ≤ 1 := by
        have h3 : C h k ∈ Set.Icc (0 : ℝ) (1 : ℝ) := hC h hh k hk
        simp at h3 ⊢
        linarith [h3.1, h3.2]
      have h6 : (h : ℝ) ≥ 1 := by
        exact_mod_cast show (h : ℕ) ≥ 1 by 
          have h7 : h ∈ Icc 1 n := hh
          simp at h7 ⊢
          omega
      have h7 : (h : ℝ) ^ 2 ≥ 1 := by
        nlinarith
      have h8 : (2 * p : ℝ) ≥ 2 := by
        have hp1 : (p : ℝ) ≥ 1 := by
          exact_mod_cast show p ≥ 1 by omega
        nlinarith
      have h9 : (C h k) - 2 * p * (h ^ 2 : ℝ) ≤ 0 := by
        nlinarith [h4, h5, h6, h7, h8]
      have h10 : (C h k) * ((C h k) - 2 * p * (h ^ 2 : ℝ)) ≤ 0 := by
        nlinarith [h4, h9]
      nlinarith
      all_goals nlinarith
    have h4 : ((C h k) / (h : ℝ)) ^ 2 ≤ 2 * p * (C h k) := by
      have h5 : (h : ℝ) > 0 := by
        have h6 : h ≥ 1 := by
          have h7 : h ∈ Icc 1 n := hh
          simp at h7 ⊢
          omega
        have h8 : (h : ℝ) ≥ 1 := by exact_mod_cast h6
        nlinarith
      have h6 : ((C h k) / (h : ℝ)) ^ 2 = ((C h k) ^ 2) / ((h : ℝ) ^ 2) := by
        field_simp
        <;> ring
      have h7 : (2 * p * (C h k) : ℝ) ≥ 0 := by
        have hp1 : (p : ℝ) ≥ 1 := by
          exact_mod_cast show p ≥ 1 by omega
        have hC1 : (C h k) ≥ 0 := by
          have h3 : C h k ∈ Set.Icc (0 : ℝ) (1 : ℝ) := hC h hh k hk
          simp at h3 ⊢
          linarith [h3.1, h3.2]
        positivity
      have h8 : ((C h k) ^ 2 : ℝ) ≤ 2 * p * (C h k) * (h ^ 2 : ℝ) := by
        linarith [h3]
      have h9 : (h : ℝ) ^ 2 > 0 := by
        have h10 : (h : ℝ) > 0 := by
          have h11 : h ≥ 1 := by
            have h12 : h ∈ Icc 1 n := hh
            simp at h12 ⊢
            omega
          have h12 : (h : ℝ) ≥ 1 := by exact_mod_cast h11
          nlinarith
        positivity
      have h11 : ((C h k) ^ 2 : ℝ) / ((h : ℝ) ^ 2) ≤ (2 * p * (C h k) * (h ^ 2 : ℝ)) / ((h : ℝ) ^ 2) := by
        apply (div_le_div_right h9).mpr
        linarith
      have h12 : (2 * p * (C h k) * (h ^ 2 : ℝ)) / ((h : ℝ) ^ 2) = (2 * p * (C h k) : ℝ) := by
        field_simp
        <;> nlinarith [show (h : ℝ) ^ 2 > 0 by positivity]
      rw [h6]
      linarith [h11, h12]
    simpa using h4
  have h3 : ∑ h ∈ Icc 1 n, ∑ k ∈ Icc 1 (p * h), ((C h k) / h) ^ 2 ≤ ∑ h ∈ Icc 1 n, ∑ k ∈ Icc 1 (p * h), (2 * p * (C h k)) := by
    apply sum_le_sum
    intro h hh
    apply sum_le_sum
    intro k hk
    have h4 : ((C h k) / h) ^ 2 ≤ 2 * p * (C h k) := h1 h hh k hk
    simpa using h4
  have h4 : ∑ h ∈ Icc 1 n, ∑ k ∈ Icc 1 (p * h), (2 * p * (C h k)) = 2 * p * ∑ h ∈ Icc 1 n, ∑ k ∈ Icc 1 (p * h), (C h k) := by
    simp [mul_sum]
    <;> ring_nf <;> simp [mul_sum]
    <;> ring
  linarith [h3, h4]