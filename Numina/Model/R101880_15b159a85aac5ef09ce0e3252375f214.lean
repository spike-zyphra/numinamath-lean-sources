import Mathlib

open Real Set
open scoped Real

theorem algebra_242025 {x : ℝ} (hx : x ∈ Ioo 0 Real.pi) :
    IsLeast {y | ∃ x : ℝ, x ∈ Ioo 0 Real.pi ∧ y = (2 - cos x) / sin x} (Real.sqrt 3) := by
  constructor
  · -- Let's first show that sqrt(3) is in the set
    use Real.pi / 3
    constructor
    · -- Verify that pi/3 is in (0, pi)
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    · -- Calculate the value at pi/3
      have h1 : cos (Real.pi / 3) = 1 / 2 := by
        rw [cos_pi_div_three]
      have h2 : sin (Real.pi / 3) = Real.sqrt 3 / 2 := by
        rw [sin_pi_div_three]
      rw [h1, h2]
      field_simp
      <;> ring_nf <;> norm_num
      <;> ring
  · -- Now we need to prove that sqrt(3) is a lower bound
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [mem_Ioo] at hx
    have h1 : 0 < sin x := by
      apply sin_pos_of_pos_of_lt_pi
      linarith [hx.1, Real.pi_pos]
      linarith [hx.2, Real.pi_pos]
    have h2 : (2 - cos x) / sin x ≥ Real.sqrt 3 := by
      have h3 : (2 - cos x) ≥ Real.sqrt 3 * sin x := by
        nlinarith [sq_nonneg (sin x - Real.sqrt 3 / 2), sq_nonneg (cos x - 1 / 2),
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sin_sq_add_cos_sq x, Real.cos_sq_add_sin_sq x]
      have h5 : 0 < sin x := by
        apply sin_pos_of_pos_of_lt_pi
        linarith [hx.1, Real.pi_pos]
        linarith [hx.2, Real.pi_pos]
      have h6 : (2 - cos x) / sin x ≥ Real.sqrt 3 := by
        apply (le_div_iff₀ h5).mpr
        linarith
      linarith
    linarith