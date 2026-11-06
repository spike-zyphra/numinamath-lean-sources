import Mathlib

open Real Set
open scoped Real

theorem calculus_22833 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = (arccos x)^2 + (arcsin x)^2) :
  image f (Icc (-1) 1) = Icc (π^2/8) (5*π^2/4) := by
  ext y
  simp only [mem_image, mem_setOf_eq, exists_prop, Icc, Set.mem_setOf_eq, and_imp]
  constructor
  · -- First direction: image f (Icc (-1) 1) ⊆ Icc (π^2/8) (5*π^2/4)
    rintro ⟨x, hx, rfl⟩
    rw [h₀]
    have h1 : -1 ≤ x ∧ x ≤ 1 := by
      exact hx
    have h2 : arcsin x = Real.pi / 2 - arccos x := by
      have h11 : arcsin x + arccos x = Real.pi / 2 := by
        have h2 : arccos x = Real.pi / 2 - arcsin x := by
          rw [Real.arccos_eq_pi_div_two_sub_arcsin]
        linarith
      linarith
    have h3 : arccos x ≥ 0 := by
      apply Real.arccos_nonneg
    have h4 : arccos x ≤ Real.pi := by
      apply Real.arccos_le_pi
    have h7 : (arccos x) ^ 2 + (arcsin x) ^ 2 ≥ Real.pi ^ 2 / 8 := by
      rw [show arcsin x = Real.pi / 2 - arccos x by linarith [h2]]
      nlinarith [sq_nonneg (arccos x - Real.pi / 4), Real.pi_pos, Real.pi_gt_three, Real.pi_gt_three]
    have h8 : (arccos x) ^ 2 + (arcsin x) ^ 2 ≤ 5 * Real.pi ^ 2 / 4 := by
      rw [show arcsin x = Real.pi / 2 - arccos x by linarith [h2]]
      nlinarith [sq_nonneg (arccos x - Real.pi), sq_nonneg (arccos x - 0), Real.pi_pos, Real.pi_gt_three]
    constructor
    · -- Show that π^2/8 ≤ (arccos x) ^ 2 + (arcsin x) ^ 2
      nlinarith
    · -- Show that the upper bound holds
      nlinarith
  · -- Reverse direction: Icc (π^2/8) (5*π^2/4) ⊆ image f (Icc (-1) 1)
    rintro ⟨hy1, hy2⟩
    have h8 : 0 ≤ Real.sqrt (8 * y - Real.pi ^ 2) := Real.sqrt_nonneg _
    have h16 : 8 * y - Real.pi ^ 2 ≥ 0 := by nlinarith [Real.pi_pos, Real.pi_gt_three, sq_nonneg (y - Real.pi ^ 2 / 8), sq_nonneg (y - Real.pi ^ 2 / 8)]
    have h9 :∃c, c = (Real.pi + Real.sqrt (8 * y - Real.pi ^ 2) ) / 4 := by
      use (Real.pi + Real.sqrt (8 * y - Real.pi ^ 2) ) / 4
    rcases h9 with ⟨c, hc⟩
    have hc_nonneg : 0 ≤ c := by
      rw [hc]
      nlinarith [Real.sqrt_nonneg (8 * y - Real.pi ^ 2), Real.pi_pos, Real.pi_gt_three, Real.sq_sqrt (show 0 ≤ (8 * y - Real.pi ^ 2 : ℝ) by linarith)]
    have hc_le_pi : c ≤ Real.pi := by
      rw [hc]
      nlinarith [Real.sqrt_nonneg (8 * y - Real.pi ^ 2), Real.pi_pos, Real.pi_gt_three, Real.sq_sqrt (show 0 ≤ (8 * y - Real.pi ^ 2 : ℝ) by linarith)]
    use Real.cos c
    constructor
    · -- Show that x is in Icc (-1) 1
      constructor
      · -- Show -1 ≤ Real.cos c
        apply Real.neg_one_le_cos
      · -- Show Real.cos c ≤ 1
        apply Real.cos_le_one
    · -- Show that f(x) = y
      rw [h₀]
      have h11 : arccos (Real.cos c) = c := by
        apply Real.arccos_cos
        all_goals nlinarith [hc_nonneg, hc_le_pi]
      have h12 : arcsin (Real.cos c) = Real.pi / 2 - c := by
        have h14 : arcsin (Real.cos c) = Real.pi / 2 - arccos (Real.cos c) := by
          rw [Real.arcsin_eq_pi_div_two_sub_arccos]
        rw [h14, h11]
        all_goals nlinarith
      rw [h11, h12]
      nlinarith [sq_nonneg (c - Real.pi / 4), Real.pi_pos, Real.pi_gt_three, Real.sq_sqrt (show 0 ≤ (8 * y - Real.pi ^ 2 : ℝ) by linarith)]