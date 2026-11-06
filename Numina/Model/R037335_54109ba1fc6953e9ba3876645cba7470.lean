import Mathlib

theorem calculus_22661 (x : ℝ) (hx : x ∈ Set.Icc 0 (2 * Real.pi)) :
    Real.sin x ^ 2 + Real.cos x + 1 = 0 ↔ x = Real.pi := by
  rcases hx with ⟨hx1, hx2⟩
  constructor
  · -- Assume $\sin^2 x + \cos x + 1 = 0$ holds, prove $x = \pi$
    intro h
    have h1 : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
      rw [Real.sin_sq]
      <;> linarith
    rw [h1] at h
    have h2 : (Real.cos x - 2) * (Real.cos x + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- $\cos x - 2 = 0$
      have h5 : Real.cos x = (2 : ℝ) := by
        linarith
      have h6 : Real.cos x ≤ 1 := by
        apply Real.cos_le_one
      nlinarith
    · -- $\cos x + 1 = 0$
      have h7 : Real.cos x = (-1 : ℝ) := by
        linarith
      have h8 : Real.sin x = 0 := by
        have h5 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
        rw [h7] at h5
        have h6 : Real.sin x ^ 2 = (0 : ℝ) := by
          nlinarith
        have h7 : Real.sin x = 0 := by
          nlinarith
        exact h7
      have h10 : ∃ k : ℤ, x = (2 * k + 1) * Real.pi := by
        rw [Real.cos_eq_neg_one_iff] at h7
        rcases h7 with ⟨k, hk⟩
        refine ⟨k, by linarith⟩
      rcases h10 with ⟨k, hk⟩
      have hk1 : (0 : ℝ) ≤ (2 * k + 1) * Real.pi := by
        nlinarith [hk, Real.pi_pos]
      have hk2 : (2 * k + 1) * Real.pi ≤ (2 * Real.pi) := by
        nlinarith [hk, Real.pi_pos]
      have hk3 : (0 : ℝ) ≤ (2 * k + 1 : ℝ) := by 
        nlinarith [show (0 : ℝ) ≤ (2 * k + 1) * Real.pi by linarith [hk1], Real.pi_pos]
      have hk4 : (2 * k + 1 : ℝ) ≤ (2 : ℝ) := by
        nlinarith [show (2 * k + 1) * Real.pi ≤ (2 * Real.pi) by linarith [hk2], Real.pi_pos]
      have hk5 : k ≥ 0 := by
        by_contra h
        push_neg at h
        have h6 : k ≤ -1 := by omega
        have h7 : (k : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast h6
        nlinarith
      have hk6 : k ≤ 0 := by
        by_contra h
        push_neg at h
        have h7 : k ≥ 1 := by omega
        have h8 : (k : ℝ) ≥ (1 : ℝ) := by exact_mod_cast h7
        nlinarith
      have hk7 : k = 0 := by
        omega
      have hk8 : x = Real.pi := by
        rw [hk]
        rw [show (k : ℝ) = (0 : ℝ) by exact_mod_cast hk7]
        norm_num
      linarith
  · -- Assume $x = \pi$, prove $\sin^2 x + \cos x + 1 = 0$
    intro h
    rw [h]
    have h1 : Real.sin (Real.pi) = 0 := Real.sin_pi
    have h2 : Real.cos (Real.pi) = -1 := Real.cos_pi
    rw [h1, h2]
    all_goals norm_num