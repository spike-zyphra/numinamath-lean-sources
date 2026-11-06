import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

/- Let $z$ be a complex number, and $|z|=1$, then the maximum and minimum values of $u=|{{z}^{2}}-z+1|$ are ___          ___. -/
theorem algebra_10714 :
  IsGreatest {u | ∃ z : ℂ, ‖z‖ = 1 ∧ u = ‖z^2 - z + 1‖} 3 ∧
  IsLeast {u | ∃ z : ℂ, ‖z‖ = 1 ∧ u = ‖z^2 - z + 1‖} 0 := by
  constructor
  · -- Show 3 is greatest
    constructor
    · -- $3$ is achievable via $z = -1$.
      use -1
      norm_num [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> norm_num [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> norm_num [Complex.ext_iff, Complex.norm_eq_abs]
      all_goals norm_num [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    · -- Show 3 is upper bound
      rintro u ⟨z, hz, rfl⟩
      have h1 : ‖z‖ = 1 := hz
      have h2 : ‖z^2 - z + 1‖ ≤ 3 := by
        have h3 : ‖z‖ = 1 := h1
        have h4 : ‖z^2 - z + 1‖ ≤ ‖z^2‖ + ‖z‖ + ‖(1 : ℂ)‖ := by
          have h1 : ‖z^2 - z + 1‖ ≤ ‖z^2 - z‖ + ‖(1 : ℂ)‖ := by
            apply norm_add_le
          have h2 : ‖z^2 - z‖ ≤ ‖z^2‖ + ‖z‖ := by
            apply norm_sub_le
          linarith [h1, h2]
        -- Simplify expressions.
        have h5 : ‖z^2‖ = ‖z‖ ^ 2 := by
          simp [norm_pow]
        rw [h5, h3] at h4
        have h6 : ‖(1 : ℂ)‖ = 1 := by
          simp
        rw [h6] at h4
        nlinarith
      linarith [h2, h1]
  · -- Show 0 is least
    constructor
    · -- Show 0 is in the set.
      use (1 + Complex.I * Real.sqrt 3) / 2
      constructor
      · -- Show that ‖z‖ = 1
        have h5 : ‖(1 + Complex.I * Real.sqrt 3) / 2‖ = 1 := by
          simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
          ring_nf
          have h6 : Real.sqrt (4: ℝ) = 2 := by 
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          norm_num [h6]
          all_goals try { tauto }
          all_goals try { nlinarith }
        exact_mod_cast h5
      · -- Show 0 = ‖z^2 - z + 1‖
        have h3 : ((1 + Complex.I * Real.sqrt 3) / 2 : ℂ) ^ 2 - ( (1 + Complex.I * Real.sqrt 3) / 2 ) + 1 = 0 := by 
          simp [pow_two, Complex.ext_iff, mul_add, mul_comm, mul_assoc]
          <;> ring_nf 
          <;> simp [Complex.I_mul_I, mul_add, mul_comm, mul_assoc, pow_two]
          <;> ring_nf 
          <;> norm_num [mul_add, mul_comm, mul_assoc, pow_two, Complex.I_mul_I, mul_assoc]
          <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (Real.sqrt 3 ^ 2)]
        have h8 : ‖((1 + Complex.I * Real.sqrt 3) / 2 : ℂ) ^ 2 - ((1 + Complex.I * Real.sqrt 3) / 2 : ℂ) + 1‖ = 0 := by 
          rw [h3]
          simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
          all_goals try { nlinarith }
        rw [h8]
        all_goals norm_num
    · -- Show 0 is minimum
      rintro u ⟨z, hz, rfl⟩
      have h1 : ‖z‖ = 1 := hz
      have h2 : ‖z^2 - z + 1‖ ≥ 0 := by
        positivity
      linarith [h2]
  all_goals try { tauto }
  <;> try { tauto }
  all_goals try { positivity }
  all_goals try { tauto }
  all_goals try { nlinarith }
  all_goals try { tauto }