import Mathlib

theorem algebra_611017: {x : ℝ | x ∈ Set.Ico 0 (2 * Real.pi) ∧ Real.sin x + Real.cos x = Real.sqrt 2} = {Real.pi / 4} := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  . -- Forward direction: if x is in the set, then x = Real.pi / 4
    intro h
    rcases h with ⟨⟨hx1, hx2⟩, h⟩
    have h1 : (Real.sin x + Real.cos x) ^ 2 = 2 := by
      calc
        _ = (Real.sqrt 2) ^ 2 := by rw [h]
        _ = 2 := Real.sq_sqrt (by linarith)
    have h2 : (Real.sin x + Real.cos x) ^ 2 = Real.sin x ^ 2 + Real.cos x ^ 2 + 2 * (Real.sin x * Real.cos x) := by ring
    rw [h2] at h1
    have h3 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    have h4 : 2 * (Real.sin x * Real.cos x) = 1 := by
      nlinarith [h1, h3]
    -- From the previous deduction `Real.sin (2 * x) = 1` 
    have h5 : Real.sin (2 * x) = 1 := by
      have h6 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by 
        rw [Real.sin_two_mul]
      nlinarith [h4, h6]
    have h6 : ∃ k : ℤ, (2 * x) = Real.pi / 2 + 2 * Real.pi * k := by
      have h7 : Real.sin (2 * x) = 1 := h5
      obtain ⟨k, hk⟩ := Real.sin_eq_one_iff.1 h7
      refine ⟨k, by linarith [hk]⟩
    rcases h6 with ⟨k, hk⟩
    have hk1 : x = Real.pi / 4 + Real.pi * k := by
      have h9 : (2 * x) = Real.pi / 2 + 2 * Real.pi * k := hk
      have h10 : x = Real.pi / 4 + Real.pi * k := by
        nlinarith
      exact h10
    have h7 : k ≥ 0 := by
      by_contra h8
      push_neg at h8
      have hk2 : k ≤ -1 := by omega
      have hk2' : (k : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast hk2
      nlinarith [Real.pi_pos, hk1, Real.pi_gt_three]
    have h8 : k ≤ 1 := by
      by_contra h9
      push_neg at h9
      have hk2 : k ≥ 2 := by omega
      have hk2' : (k : ℝ) ≥ 2 := by exact_mod_cast hk2
      nlinarith [Real.pi_pos, hk1, Real.pi_gt_three]
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with h10 | h11
    · -- k = 0
      have hk0 : (k : ℝ) = 0 := by exact_mod_cast h10
      have hx0 : x = Real.pi / 4 := by 
        rw [hk0] at hk1 
        linarith
      linarith
    · -- k = 1
      have hk1' : (k : ℝ) = 1 := by exact_mod_cast h11
      have hx11 : x = 5 * Real.pi / 4 := by
        rw [hk1'] at hk1 
        linarith
      -- Now $\sin x + \cos x = -\sqrt{2}$, which contradicts $\sin x + \cos x = \sqrt{2}$
      have h7 : Real.sin x + Real.cos x = -Real.sqrt 2 := by
        rw [show x = 5 * Real.pi / 4 by linarith]
        have h8 : Real.sin (5 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
          have h9 : 5 * Real.pi / 4 = Real.pi + Real.pi / 4 := by ring
          rw [h9]
          have h10 : Real.sin (Real.pi + Real.pi / 4) = -Real.sin (Real.pi / 4) := by
            rw [Real.sin_add, Real.sin_pi, Real.cos_pi]
            ring
          rw [h10]
          have h11 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
          rw [h11]
          ring
        have h9 : Real.cos (5 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
          have h10 : 5 * Real.pi / 4 = Real.pi + Real.pi / 4 := by ring
          rw [h10]
          have h11 : Real.cos (Real.pi + Real.pi / 4) = -Real.cos (Real.pi / 4) := by 
            rw [Real.cos_add, Real.sin_pi, Real.cos_pi]
            ring
          rw [h11]
          have h12 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
          rw [h12]
          ring
        rw [h8, h9]
        ring
      nlinarith [Real.sqrt_pos.mpr (show (0: ℝ) < (2: ℝ) by linarith), Real.sq_sqrt (show (0: ℝ) ≤ (2: ℝ) by linarith)]
  . -- Backward direction: if x = Real.pi / 4, then x is in the set
    intro h
    rw [h]
    constructor
    . -- Show Real.pi / 4 ∈ Ico [0, 2 * Real.pi)
      constructor
      · -- Show 0 ≤ Real.pi / 4
        linarith [Real.pi_pos]
      · -- Show Real.pi / 4 < 2 * Real.pi
        linarith [Real.pi_pos]
    . -- Show Real.sin (Real.pi / 4) + Real.cos (Real.pi / 4) = Real.sqrt 2
      have h1 : Real.sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
      have h2 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      rw [h1, h2]
      ring