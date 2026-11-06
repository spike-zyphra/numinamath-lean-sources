import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_157709 {f : ℝ → ℝ} (hf : f = λ x => cos (sin x)) :
    IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} (Real.pi) := by 
  constructor
  · -- We need to prove $\pi$ is a positive period
    constructor
    · -- Show $\pi > 0$
      exact pi_pos
    · -- Show $f = \lambda x, f (x + \pi)$
      funext x
      rw [hf]
      simp [Real.sin_add, Real.cos_pi, Real.sin_pi]
      <;> ring_nf <;> simp [Real.cos_sq]
      <;> ring
  · -- Show $\pi$ is the smallest positive period
    intro T ⟨ht_pos, ht_period⟩
    by_contra h
    push_neg at h
    have h1 := congr_fun ht_period 0
    simp [hf] at h1
    have h2 : Real.sin T > 0 := by
      apply Real.sin_pos_of_pos_of_lt_pi
      linarith
      linarith
    have h3 : Real.cos (Real.sin T) = 1 := by 
      linarith
    have h4 : ∃ k : ℤ, Real.sin T = (2 * k : ℝ) * Real.pi := by
      rw [Real.cos_eq_one_iff] at h3
      rcases h3 with ⟨k, hk⟩
      use k
      linarith
    rcases h4 with ⟨k, hk⟩
    have h5 : (2 * k : ℝ) * Real.pi > (0 : ℝ) := by 
      nlinarith [Real.pi_pos, h2]
    have h6 : k ≥ 0 := by 
      by_contra hk2
      push_neg at hk2
      have : (k : ℝ) < (0 : ℝ) := by 
        exact_mod_cast hk2
      nlinarith [Real.pi_pos]
    have h7 : k = 0 := by 
      by_contra hk2
      push_neg at hk2
      have h8 : (2 * k : ℝ) * Real.pi ≥ (2 * (1 : ℝ) * Real.pi) := by
        have : (k : ℝ) ≥ (1 : ℝ) := by 
          have hk5 : k ≥ 1 := by omega
          exact_mod_cast hk5
        nlinarith
      have h9 : Real.sin T ≥ (2 * (1 : ℝ) * Real.pi) := by
        nlinarith [show Real.sin T = (2 * k : ℝ) * Real.pi by linarith [hk], h8]
      have h10 : Real.sin T ≥ Real.pi := by
        nlinarith [h9]
      have h11 : Real.sin T ≤ 1 := by 
        apply Real.sin_le_one
      nlinarith [Real.pi_gt_three, h10, h11]
    have hk1 : k = 0 := by 
      omega
    rw [hk1] at hk
    norm_num at hk
    linarith [Real.pi_pos, hk, Real.sin_pos_of_pos_of_lt_pi ht_pos (show T < Real.pi by linarith)]