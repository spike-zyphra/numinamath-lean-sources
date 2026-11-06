import Mathlib

open Real

theorem algebra_608562 (f : ℝ → ℝ) (hf : ∀ x, f x = cos (cos x)):
    IsLeast {T : ℝ | 0 < T ∧ ∀ x, f (x + T) = f x} π := by
  constructor
  · -- Show that π is in the set
    constructor
    · -- Show that 0 < π
      exact pi_pos
    · -- Show that ∀ x, f (x + π) = f x
      intro x
      have h1 : f (x + π) = f x := by
        rw [hf, hf]
        have h2 : cos (x + π) = - cos x := by
          rw [cos_add_pi]
        have h3 : cos (cos (x + π)) = cos (cos x) := by
          rw [h2]
          have h4 : cos (- cos x) = cos (cos x) := by
            rw [cos_neg]
          linarith
        linarith
      exact h1
  · -- Show that π is the least element in the set
    intro T hT
    rcases hT with ⟨hT_pos, hT_period⟩
    by_contra h
    push_neg at h
    -- Assume T is a positive period with T < π
    have h1 := hT_period (Real.pi / 2 - T)
    have h2 : f (Real.pi / 2 - T + T) = f (Real.pi / 2 - T) := by
      simpa using h1
    -- Simplify f (Real.pi / 2 - T + T) = f (Real.pi / 2)
    have h3 : f (Real.pi / 2 - T + T) = f (Real.pi / 2) := by
      have h4 : Real.pi / 2 - T + T = Real.pi / 2 := by
        ring
      rw [h4]
    -- Combining h2 and h3, we get f (Real.pi / 2) = f (Real.pi / 2 - T)
    have h4 : f (Real.pi / 2) = f (Real.pi / 2 - T) := by
      linarith [h2, h3]
    -- Compute f (Real.pi / 2) = 1
    have h5 : f (Real.pi / 2) = 1 := by
      rw [hf]
      have h6 : cos (Real.pi / 2) = 0 := by
        exact cos_pi_div_two
      have h7 : cos (cos (Real.pi / 2)) = 1 := by
        rw [h6]
        norm_num
      linarith
    -- Compute f (Real.pi / 2 - T) = cos (sin T)
    have h8 : f (Real.pi / 2 - T) = cos (sin T) := by
      rw [hf]
      have h9 : cos (Real.pi / 2 - T) = sin T := by
        rw [cos_pi_div_two_sub]
      rw [h9]
    -- From h4, we get 1 = cos (sin T)
    rw [h5, h8] at h4
    -- We have sin T > 0
    have h10 : sin T > 0 := by
      apply sin_pos_of_pos_of_lt_pi
      all_goals linarith [show T > 0 by linarith, show T < Real.pi by linarith, Real.pi_pos]
    -- From cos (sin T) = 1 and sin T > 0, we get a contradiction
    have h11 : cos (sin T) = 1 := by
      linarith
    -- From cos(y) = 1, we get y = 2kπ for some integer k
    have h12 : ∃ k : ℤ, sin T = 2 * Real.pi * (k : ℝ) := by
      have h13 : cos (sin T) = 1 := h11
      rw [cos_eq_one_iff] at h13
      obtain ⟨k, hk⟩ := h13
      use k
      all_goals
        try linarith
    rcases h12 with ⟨k, hk⟩
    -- Now, sin T = 2πk for some integer k
    -- If k ≤ 0, then sin T ≤ 0, contradicts with sin T > 0
    have h14 : k > 0 := by
      by_contra h
      push_neg at h
      have h15 : k ≤ 0 := by omega
      have h16 : (k : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h15
      have h17 : sin T ≤ 0 := by
        nlinarith [Real.pi_pos, show (k : ℝ) ≤ 0 by linarith, hk]
      linarith [show sin T > 0 by linarith [h10], h17]
    -- If k ≥ 1, then sin T ≥ 2π
    have h15 : k ≥ 1 := by omega
    have h16 : (k : ℝ) ≥ (1 : ℝ) := by exact_mod_cast show (k : ℝ) ≥ (1 : ℝ) by exact_mod_cast h15
    have h17 : sin T ≥ 2 * Real.pi := by
      nlinarith [Real.pi_pos, show (k : ℝ) ≥ 1 by linarith, hk]
    -- But sin T ≤ 1 for all real numbers
    have h18 : sin T ≤ 1 := by
      apply sin_le_one
    -- Since 2π > 1, we get a contradiction
    have h19 : 2 * Real.pi > (1 : ℝ) := by
      linarith [Real.pi_gt_three]
    linarith [h17, h18, h19]