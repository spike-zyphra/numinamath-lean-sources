import Mathlib

/-If $m$ is a real number and $2x^2+mx+8$ has two distinct real roots, then what are the possible values of $m$?  Express your answer in interval notation.-/
theorem algebra_18869 (m : ℝ) (h : ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ 2*x1^2+m*x1+8=0 ∧ 2*x2^2+m*x2+8=0) :
    m < -8 ∨ m > 8 := by
  -- If a quadratic have two root, then its discriminant is positive.
  have : 0 < discrim 2 m 8 := by
    rcases h with ⟨x₁, x₂, hx, hx₁, hx₂⟩
    rw [pow_two] at hx₁ hx₂
    have d₁ := discrim_eq_sq_of_quadratic_eq_zero hx₁
    have d₂ := discrim_eq_sq_of_quadratic_eq_zero hx₂
    have : discrim 2 m 8 ≠ 0 := by
      intro h
      rw [h, Eq.comm] at d₁ d₂
      simp at d₁ d₂
      absurd hx
      linarith
    rw [d₁]
    apply sq_pos_of_ne_zero
    intro h
    rw [h] at d₁
    simp at d₁
    absurd this
    linarith
  -- discrim 2 m 8 := m^2 - 4 * 2 * 8
  rw [discrim] at this
  have : 8^2 < m^2 := by linarith
  rw [sq_lt_sq] at this
  simp at this
  rw [lt_abs] at this
  simp
  obtain (r | r) := this
  · apply Or.inr (by linarith)
  · apply Or.inl (by linarith)
