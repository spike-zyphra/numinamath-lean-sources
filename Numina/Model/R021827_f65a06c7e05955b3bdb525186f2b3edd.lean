import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem inequalities_135495
  (a b c d : EuclideanSpace ℝ (Fin 2))
  (h₀ : ¬ Collinear ℝ {a, b})
  (h₁ : ¬ Collinear ℝ {a, c})
  (h₂ : ¬ Collinear ℝ {a, d})
  (h₃ : ¬ Collinear ℝ {b, c})
  (h₄ : ¬ Collinear ℝ {b, d})
  (h₅ : ¬ Collinear ℝ {c, d})
  (h₆ : a + b + c + d = 0) :
  ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ > ‖a + b‖ + ‖a + c‖ + ‖a + d‖ := by
  simp [collinear_pair] at h₀ h₁ h₂ h₃ h₄ h₅
  all_goals
  try { tauto }
  all_goals
  norm_num [collinear_pair] at h₀ h₁ h₂ h₃ h₄ h₅ ⊢
  all_goals
  try { tauto }
  all_goals
  norm_num [Real.sqrt_pos.mpr] at h₀ h₁ h₂ h₃ h₄ h₅ ⊢
  all_goals
  try { nlinarith [sq_pos_of_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)] }