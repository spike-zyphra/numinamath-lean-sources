import Mathlib

open Finset ENNReal

theorem algebra_464695 (p : ENNReal) (ple : p ≤ 1)
  (hp : ∑ X : {i : Fin 3 // 1 ≤ i.val}, PMF.binomial p ple 2 X = 5 / 9) :
  ∑ Y : Fin 4, (3 * Y + 1) * PMF.binomial p ple 3 Y = 4 := by
  have PXsum1 := (PMF.binomial p ple 2).tsum_coe
  have PYsum1 := (PMF.binomial p ple 3).tsum_coe
  simp [tsum_fintype, sum_fin_eq_sum_range, show range 3 = {0,1,2} by decide] at PXsum1
  simp [tsum_fintype] at PYsum1
  rw [← sum_toFinset_eq_subtype] at hp
  simp [show {x : Fin 3 | 1 ≤ x.val}.toFinset = {1, 2} by decide] at hp
  rw [hp] at PXsum1; apply_fun fun t => t.toReal at PXsum1
  rw [toReal_add, toReal_pow, toReal_sub_of_le] at PXsum1; simp at PXsum1
  replace PXsum1 : (1 - p.toReal) ^ 2 = (2 / 3) ^ 2 := by linarith
  rw [pow_left_inj₀] at PXsum1; replace PXsum1 : p.toReal = 1 / 3 := by linarith
  rw [← toReal_eq_toReal, toReal_sum, sum_fin_eq_sum_range]
  simp [show range 4 = {0,1,2,3} by decide, PMF.binomial_apply, toReal_pow]
  rw [toReal_sub_of_le, PXsum1]; norm_num
  any_goals exact ple
  any_goals simp
  intro x hx; apply_fun fun t => t.toReal at hx; simp at hx
  rcases hx with hx|hx
  · rw [toReal_add] at hx; simp at hx
    suffices : (0 : ℝ) ≤ x; linarith; positivity
    apply coe_ne_top; simp
  simp [PMF.binomial_apply, or_assoc] at hx; rcases hx with hx|hx|hx
  any_goals linarith
  rw [toReal_sub_of_le] at hx; simp at hx; linarith
  exact ple; simp
  suffices : 0 < Nat.choose 3 x; omega; apply Nat.choose_pos; exact Fin.is_le x
  intro x hx; apply_fun fun t => t.toReal at hx; simp at hx
  rcases hx with hx|hx
  · rw [toReal_add] at hx; simp at hx
    suffices : (0 : ℝ) ≤ x; linarith; positivity
    apply coe_ne_top; simp
  simp [PMF.binomial_apply, or_assoc] at hx; rcases hx with hx|hx|hx
  any_goals linarith
  rw [toReal_sub_of_le] at hx; simp at hx; linarith
  exact ple; simp
  suffices : 0 < Nat.choose 3 x; omega; apply Nat.choose_pos; exact Fin.is_le x
  apply toReal_le_of_le_ofReal; any_goals simp
  exact ple; rw [show (5 : ENNReal) / 9 = (5 / 9 : NNReal) by simp]; apply coe_ne_top