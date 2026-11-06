import Mathlib

theorem algebra_27100 {f : ℝ → ℝ} (h : ∀ x, f (Real.cos x) = Real.cos (17 * x)) :
    ∀ x, f (Real.sin x) = Real.sin (17 * x) := by
  intro x
  have h1 : f (Real.sin x) = Real.cos (17 * (Real.pi / 2 - x)) := by
    have h2 : Real.sin x = Real.cos (Real.pi / 2 - x) := by
      rw [← Real.cos_pi_div_two_sub x]
    rw [h2]
    specialize h (Real.pi / 2 - x)
    simpa using h
  have h3 : Real.cos (17 * (Real.pi / 2 - x)) = Real.sin (17 * x) := by
    have h4 : 17 * (Real.pi / 2 - x) = Real.pi / 2 - 17 * x + 8 * Real.pi := by
      ring_nf
    have h5 : Real.cos (17 * (Real.pi / 2 - x)) = Real.cos (Real.pi / 2 - 17 * x + 8 * Real.pi) := by 
      rw [h4]
    have h6 : Real.cos (Real.pi / 2 - 17 * x + 8 * Real.pi) = Real.cos (Real.pi / 2 - 17 * x) := by 
      have h7 : Real.cos (Real.pi / 2 - 17 * x + 8 * Real.pi) = Real.cos (Real.pi / 2 - 17 * x) := by 
        have h8 : Real.pi / 2 - 17 * x + 8 * Real.pi = Real.pi / 2 - 17 * x + 4 * (2 * Real.pi) := by 
          ring_nf
        rw [h8]
        have h9 : Real.cos (Real.pi / 2 - 17 * x + 4 * (2 * Real.pi)) = Real.cos (Real.pi / 2 - 17 * x) := by
          have h10 : Real.cos (Real.pi / 2 - 17 * x + 4 * (2 * Real.pi)) = Real.cos (Real.pi / 2 - 17 * x) := by 
            have h11 : 4 * (2 * Real.pi) = (4 : ℕ) * (2 * Real.pi) := by 
              ring_nf
            rw [h11]
            rw [Real.cos_add_nat_mul_two_pi]
          exact h10
        exact h9
      exact h7
    have h7 : Real.cos (Real.pi / 2 - 17 * x) = Real.sin (17 * x) := by 
      have h8 : Real.cos (Real.pi / 2 - 17 * x) = Real.sin (17 * x) := by 
        rw [Real.cos_pi_div_two_sub]
        <;> ring_nf
      exact h8
    rw [h5, h6, h7]
  rw [h1, h3]
  all_goals try ring_nf <;> simp [Real.sin_pi_div_two, Real.sin_sub, Real.sin_pi_div_two]