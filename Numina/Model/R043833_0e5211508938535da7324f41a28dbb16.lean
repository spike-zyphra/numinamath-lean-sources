import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_206430 (e a : EuclideanSpace ℝ (Fin 2))
  (h₀ : ‖e‖ = 1) (h₁ : inner a e = (2: ℝ))
  (h₂ : ∀ t : ℝ, ‖a‖^2 ≤ 5 * ‖a + t • e‖) :
  ‖a‖ ∈ Set.Icc (√5) (2 * √5) := by
  have h3 : ∀ t : ℝ, 0 ≤ 25 * (t * t) + 100 * t + (25 * ‖a‖^2 - ‖a‖^4) := by
    intro t
    have h := sq_le_sq₀ (by positivity) (by positivity) |>.mpr (h₂ t)
    ring_nf at h
    rw [norm_add_sq_real a (t • e)] at h
    rw [norm_smul, real_inner_smul_right, h₁, h₀] at h
    simp at h
    linarith
  -- quadratic equation always being nonegative means disriminant is nonnegative
  have h4 : (100 : ℝ) ^ 2 - 4 * (25 : ℝ) * (25 * ‖a‖^2 - ‖a‖^4) ≤ 0 := by
    specialize h3 (- (100 : ℝ) / (2 * 25))
    nlinarith
  have h5 : ‖a‖^4 - 25 * ‖a‖^2 + 100 ≤ 0 := by
    nlinarith
  have h6 : 5 ≤ ‖a‖^2 ∧ ‖a‖^2 ≤ 20 := by
    constructor
    · -- Solving quadratic inequality $‖a‖^4 - 25‖a‖^2 + 100 \leq 0$ gives lower bound $5 \leq ‖a‖^2$
      nlinarith [sq_nonneg (‖a‖^2 - 5), sq_nonneg (‖a‖^2 - 20)]
    · -- Solving quadratic inequality $‖a‖^4 - 25‖a‖^2 + 100 \leq 0$ gives upper bound $‖a‖^2 \leq 20$
      nlinarith [sq_nonneg (‖a‖^2 - 5), sq_nonneg (‖a‖^2 - 20)]
  have h7 : √5 ≤ ‖a‖ := by
    have h8 : (√5 : ℝ) ≤ ‖a‖ := by
      have h9 : (√5 : ℝ) ^ 2 ≤ ‖a‖ ^ 2 := by
        have h10 : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
        linarith [h6.1, h10]
      have h11 : 0 ≤ (‖a‖ : ℝ) := by positivity
      have h12 : 0 ≤ (Real.sqrt 5 : ℝ) := Real.sqrt_nonneg 5
      nlinarith [h9, Real.sqrt_nonneg 5, positivity]
    linarith
  have h8 : ‖a‖ ≤ 2 * √5 := by
    have h9 : ‖a‖^2 ≤ 20 := by
      linarith [h6.2]
    have h10 : ‖a‖ ≤ Real.sqrt 20 := by
      have h11 : ‖a‖ ^ 2 ≤ (20 : ℝ) := by linarith [h6.2]
      have h12 : 0 ≤ (‖a‖ : ℝ) := by positivity
      have h13 : ‖a‖ ≤ Real.sqrt 20 := by
        apply Real.le_sqrt_of_sq_le
        linarith
      linarith
    have h14 : Real.sqrt 20 = 2 * Real.sqrt 5 := by
      calc
        Real.sqrt 20 = Real.sqrt (2^2 * 5) := by norm_num
        _ = (2 : ℝ) * Real.sqrt 5 := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    linarith [h10, h14]
  constructor
  · exact h7
  · exact h8