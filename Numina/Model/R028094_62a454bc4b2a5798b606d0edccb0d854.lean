import Mathlib

theorem algebra_193347 (a : ℝ) :
    (∀ b : ℝ, ∃ x y : ℝ, 2^(b * x) + (a + 1) * b * y^2 = a^2 ∧ (a - 1) * x^3 + y^3 = 1) ↔
    a = -1 := by
  constructor
  · -- Assume the system has solutions for all b, prove a = -1.
    intro h
    -- First, set b = 0 to obtain either a = 1 or a = -1.
    have h1 := h 0
    rcases h1 with ⟨x, y, h_eq1, h_eq2⟩
    have h_eq1' : a^2 = 1 := by
      simp [Real.rpow_zero, mul_zero, add_zero] at h_eq1
      linarith
    have h_a_p1 : a = 1 ∨ a = -1 := by
      rw [sq_eq_one_iff] at h_eq1'
      exact h_eq1'
    rcases h_a_p1 with ha1 | ha1
    · -- Suppose a = 1, show contradiction via b = 1.
      rw [ha1] at h_eq1 h_eq2
      have h_eq2' : (1 - 1 : ℝ) * x^3 + y^3 = 1 := by
        linarith
      have hy : y^3 = 1 := by 
        simp at h_eq2'
        nlinarith
      have h2 := h 1
      rcases h2 with ⟨x1, y1, h_eq1_b1, h_eq2_b1⟩
      rw [ha1] at h_eq1_b1 h_eq2_b1
      have hy1 : y1^3 = 1 := by 
        simp at h_eq2_b1
        nlinarith
      have hy1_eq1 : y1 = 1 := by
        have h1 : y1^3 - 1 = 0 := by linarith
        have h2 : (y1 - 1) * (y1^2 + y1 + 1) = 0 := by 
          ring_nf at h1 ⊢
          linarith
        cases' (mul_eq_zero.mp h2) with h3 h4
        · -- Let's try h3: y1 - 1 = 0, hence y1 = 1
          linarith
        · -- Let's try h4: y1^2 + y1 + 1 = 0, which is impossible
          have h5 : y1^2 + y1 + 1 > 0 := by 
            nlinarith [sq_nonneg (y1 + 1/2)]
          linarith
      rw [hy1_eq1] at h_eq1_b1
      have h_eq1_b1' : (2 : ℝ) ^ (1 * x1) + (1 + 1) * 1 * (1: ℝ)^2 = (1 : ℝ) ^ 2 := by 
        linarith
      have h_eq1_b1'' : (2 : ℝ) ^ (1 * x1) = -1 := by
        nlinarith
      have h_absurd : (2 : ℝ) ^ (1 * x1) > 0 := by
        positivity
      linarith
    · -- From previous proof, a = 1 gives contradiction, therefore a = -1.
      exact ha1
  · -- Assume a = -1, prove the system has solutions for all b.
    intro ha b
    use (0 : ℝ), (1 : ℝ)
    rw [ha]
    constructor
    · -- First equation
      simp [Real.rpow_zero, mul_zero, add_zero]
      all_goals norm_num
    · -- Second equation
      norm_num