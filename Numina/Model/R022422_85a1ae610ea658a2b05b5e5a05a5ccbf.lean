import Mathlib

theorem algebra_151007 {z : ℂ} (hz : ∃ a b : ℝ, z = a + b * .I ∧ b ≠ 0) :
    ‖z ^ 2‖ = ‖z‖ ^ 2 ∧ ¬(z ^ 2 = ‖z‖ ^ 2) := by 
  rcases hz with ⟨a, b, h_eq, hb⟩
  have eq1 : ‖z ^ 2‖ = ‖z‖ ^ 2 := by
    rw [h_eq]
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf
    <;> norm_num
  constructor
  · -- Proof that `‖z ^ 2‖ = ‖z‖ ^ 2`
    exact eq1
  · -- Proof that `z ^ 2 ≠ ‖z‖ ^ 2`
    by_contra h
    rw [h_eq] at h
    simp [Complex.ext_iff, pow_two, Complex.norm_eq_abs, Complex.abs, Complex.normSq] at h 
    ring_nf at h 
    -- Now h is a conjunction where the second part is `2 * a * b = 0`
    -- The first part is a^2 - b^2 = a^2 + b^2
    have h1 : b ^ 2 = 0 := by 
      nlinarith 
    have hb0 : b = 0 := by
      nlinarith
    contradiction