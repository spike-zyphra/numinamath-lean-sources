import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_116975 {f : ℝ → ℝ} (hf : f = λ x => 4 * π * arcsin x - (arccos (-x))^2)
  (M m : ℝ) (hM : ∃ x, f x = M) (hm : ∃ x, f x = m)
  (hMub : ∀ x, f x ≤ M) (hmub : ∀ x, f x ≥ m) :
  M - m = 3 * π^2 := by

  have h1 : ∀ x, f x = 4 * π * arcsin x - (arccos (-x)) ^ 2 := by
    intro x
    rw [hf]

  have h2 : ∀ x, f x = - (arcsin x) ^ 2 + 3 * π * arcsin x - (π ^ 2 / 4) := by
    intro x
    rw [h1 x]
    have h4 : arccos (-x) = π / 2 + arcsin x := by
      have h5 : arccos (-x) = π - arccos x := by
        have h6 : arccos (-x) = π - arccos x := by
          rw [Real.arccos_neg]
        linarith
      have h8 : arccos x = π / 2 - arcsin x := by
        rw [Real.arccos_eq_pi_div_two_sub_arcsin]
      rw [h5, h8]
      all_goals ring
    rw [h4]
    nlinarith [Real.arcsin_le_pi_div_two x, Real.neg_pi_div_two_le_arcsin x, Real.pi_pos]

  have h3 : arcsin (1 : ℝ) = π / 2 := by
    rw [Real.arcsin_one]

  have h5 : arcsin (-1 : ℝ) = - (π / 2) := by
    have h2 : arcsin (-1 : ℝ) = -(arcsin (1 : ℝ)) := by
      rw [Real.arcsin_neg]
    rw [h2, h3]
    <;> nlinarith [Real.pi_pos]

  have h6 : f (1 : ℝ) = π^2 := by
    rw [h2 1]
    rw [h3]
    nlinarith [Real.pi_pos]

  have h7 : f (-1 : ℝ) = -2 * π ^ 2 := by
    rw [h2 (-1 : ℝ)]
    rw [h5]
    nlinarith [Real.pi_pos]

  have h8 : M ≥ π ^ 2 := by
    have h9 : ∃ x, f x = M := hM
    rcases h9 with ⟨x, hx⟩
    have h10 : f (1 : ℝ) = π^2 := h6
    have h11 : f (1 : ℝ) ≤ M := hMub (1 : ℝ)
    nlinarith [h10, h11, hx]

  have h9 : ∀ x, f x ≤ π ^ 2 := by 
    intro x 
    rw [h2 x] 
    nlinarith [ sq_nonneg (arcsin x - 3 * π / 2), sq_nonneg (arcsin x - π / 2), sq_nonneg (arcsin x + π / 2), Real.arcsin_le_pi_div_two x, Real.neg_pi_div_two_le_arcsin x, Real.pi_pos, Real.pi_gt_three, mul_nonneg (show 0 ≤ (Real.pi - (0 : ℝ)) by linarith [Real.pi_pos]) (show 0 ≤ (Real.pi - (0 : ℝ)) by linarith [Real.pi_pos])]
  
  have h11' : M ≤ π ^ 2 := by
    rcases hM with ⟨x0, hx0⟩
    have eq1 : f x0 = M := hx0
    have eq2 : f x0 ≤ π ^ 2 := by
      specialize h9 x0
      linarith
    linarith [eq1, eq2]

  have hM' : M = π ^ 2 := by
    linarith [h8, h11']

  have h10' : ∀ x, f x ≥ -2 * π ^ 2 := by 
    intro x 
    rw [h2 x] 
    nlinarith [ sq_nonneg (arcsin x + π / 2), sq_nonneg (arcsin x - (3 * π / 2)), sq_nonneg (arcsin x - π / 2), sq_nonneg (arcsin x + (π / 2)), Real.arcsin_le_pi_div_two x, Real.neg_pi_div_two_le_arcsin x, Real.pi_pos, Real.pi_gt_three, mul_nonneg (show 0 ≤ (Real.pi - (0 : ℝ)) by linarith [Real.pi_pos]) (show 0 ≤ (Real.pi - (0 : ℝ)) by linarith [Real.pi_pos]) ]

  have h11'' : m ≤ -2 * π ^ 2 := by 
    have eq1 := hmub (-1 : ℝ)
    have eq2 : f (-1 : ℝ) = -2 * π ^ 2 := h7
    linarith [eq1, eq2]

  -- Prove `m \ge -2π^2`.
  -- For this, we need that there exists some x such that f(x) = m.
  have h12' : m ≥ -2 * π ^ 2 := by
    rcases hm with ⟨x0, hx0⟩
    have eq1 : f x0 = m := hx0
    have eq2 : f x0 ≥ -2 * π ^ 2 := by 
      specialize h10' x0 
      linarith 
    linarith [eq1, eq2]

  have hm' : m = -2 * π ^ 2 := by 
    linarith [h11'', h12']

  linarith [hM', hm']