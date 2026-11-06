import Mathlib

theorem algebra_115009 {x y z : ℝ} (h₀ : x = (y + z) ^ 2) (h₁ : y = (x + z) ^ 2)
    (h₂ : z = (x + y) ^ 2) :
    (x = 0 ∧ y = 0 ∧ z = 0) ∨ (x = 1 / 4 ∧ y = 1 / 4 ∧ z = 1 / 4) := by

  have h4 : x = (y + z) ^ 2 := h₀
  have h5 : y = (x + z) ^ 2 := h₁
  have h6 : z = (x + y) ^ 2 := h₂

  have h7 : (x - y) * (1 + 2 * z + x + y) = 0 := by
    nlinarith

  by_cases h10 : x - y = 0

  · -- x = y
    have h11 : x = y := by linarith
    have h12 : x = (x + z) ^ 2 := by 
      rw [show y = x by linarith [h11] ] at h₀
      nlinarith 
    have h13 : z = 4 * x ^ 2 := by
      have h14 : z = (x + y) ^ 2 := h₂ 
      rw [show y = x by linarith [h11] ] at h14
      nlinarith 
    rw [show z = 4 * x ^ 2 by linarith [h13] ] at h12
    have h14 : x = (x + 4 * x^2) ^ 2 := by linarith 
    have h15 : x = 0 ∨ x = 1 / 4 := by 
      have h15_eq : x * (x - 1 / 4) = 0 := by 
        nlinarith [sq_nonneg (x - 1 / 4), sq_nonneg (z - 0), sq_nonneg (x * (x - 1 / 4))]
      cases (mul_eq_zero.mp h15_eq) with 
      | inl h16 => 
        left 
        linarith 
      | inr h17 => 
        right 
        linarith 
    cases h15 with 
    | inl hx0 => 
      have hx : x = 0 := hx0 
      have hy : y = 0 := by linarith [h11, hx0] 
      have hz : z = 0 := by 
        rw [hx] at h13 
        nlinarith 
      left 
      exact ⟨hx, hy, hz⟩ 
    | inr hx14 => 
      have hx : x = 1 / 4 := by linarith 
      have hy : y = 1 / 4 := by linarith [h11, hx14] 
      have hz : z = 1 / 4 := by 
        rw [hx14] at h13 
        nlinarith 
      right 
      exact ⟨by linarith, by linarith, by linarith⟩

  · -- x - y ≠ 0 
    have eq1 : 1 + 2 * z + x + y = 0 := by 
      by_contra h'
      -- Assume that 1 + 2 * z + x + y ≠ 0.
      -- From h7: (x - y) * (1 + 2 * z + x + y) = 0.
      -- Since 1 + 2 * z + x + y ≠ 0 (by h'), we have x - y = 0.
      have h8 : x - y ≠ 0 := by intro heq; apply h10; linarith 
      have h9 : (x - y) * (1 + 2 * z + x + y) = 0 := h7
      have h10' : 1 + 2 * z + x + y ≠ 0 := by 
        intro heq'
        apply h'
        linarith 
      -- Now h9 becomes (x - y) * K = 0, where K ≠ 0. This forces x - y = 0.
      have h9_eq : x - y = 0 := by 
        apply_fun (fun k => k / (1 + 2 * z + x + y)) at h9
        field_simp [h10'] at h9 
        all_goals linarith 
      -- x - y = 0 and x - y ≠ 0 is a contradiction.
      exfalso 
      apply h10 
      linarith 
    -- From eq1: 1 + 2 * z + x + y = 0. Since variables are non-negative by definition.
    -- Adding the positive derivatives and squares.
    have eq2 : x ≥ 0 := by 
      nlinarith [sq_nonneg (y + z), sq_nonneg (x + z), sq_nonneg (x + y)]
    have eq3 : y ≥ 0 := by 
      nlinarith [sq_nonneg (y + z), sq_nonneg (x + z), sq_nonneg (x + y)]
    have eq4 : z ≥ 0 := by 
      nlinarith [sq_nonneg (y + z), sq_nonneg (x + z), sq_nonneg (x + y)]
    have eq5 : x = 0 := by 
      nlinarith 
    have eq6 : y = 0 := by 
      nlinarith 
    have eq7 : z = 0 := by 
      nlinarith 
    left 
    exact ⟨eq5, eq6, eq7⟩