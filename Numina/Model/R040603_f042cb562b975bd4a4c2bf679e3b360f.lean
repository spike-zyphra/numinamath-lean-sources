import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_206920 (f : ℝ → ℝ) (hf : f = λ x => ⌊x⌋ + Real.sqrt (x - ⌊x⌋)) :
    StrictMono f := by
  intro x y hxy
  have hfx : f x = (⌊x⌋ : ℝ) + Real.sqrt (x - ⌊x⌋) := by 
    rw [hf]
  have hfy : f y = (⌊y⌋ : ℝ) + Real.sqrt (y - ⌊y⌋) := by 
    rw [hf]
  rw [hfx, hfy]
  by_cases h1 : ⌊x⌋ < ⌊y⌋
  · -- case where `⌊x⌋ < ⌊y⌋`
    have h2 : ⌊x⌋ + 1 ≤ ⌊y⌋ := by
      omega
    have h3 : (⌊x⌋ : ℝ) < (⌊y⌋ : ℝ) := by
      exact_mod_cast h1
    have h4 : Real.sqrt (x - ⌊x⌋) < 1 := by
      have h5 : x - ⌊x⌋ < 1 := by
        have h6 : x < ⌊x⌋ + 1 := by 
          exact Int.lt_floor_add_one x
        linarith
      have h7 : Real.sqrt (x - ⌊x⌋) < Real.sqrt (1 : ℝ) := by
        apply Real.sqrt_lt_sqrt
        · -- Show 0 <= x - floor x 
          have h8 : x - ⌊x⌋ ≥ 0 := by
            have h9 : ⌊x⌋ ≤ x := Int.floor_le x
            linarith
          linarith 
        · -- Show x - floor x < 1
          linarith [h5]
      have h8 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
      linarith [h8, h7]
    have h11 : (⌊x⌋ : ℝ) + Real.sqrt (x - ⌊x⌋) < (⌊y⌋ : ℝ) := by
      have h12 : (⌊x⌋ : ℝ) + Real.sqrt (x - ⌊x⌋) < (⌊x⌋ : ℝ) + 1 := by
        nlinarith [Real.sqrt_nonneg (x - ⌊x⌋), h4]
      have h13 : (⌊x⌋ : ℝ) + 1 ≤ (⌊y⌋ : ℝ) := by
        exact_mod_cast (show ⌊x⌋ + 1 ≤ ⌊y⌋ by omega)
      linarith [h12, h13]
    have h10 : (⌊y⌋ : ℝ) ≤ (⌊y⌋ : ℝ) + Real.sqrt (y - ⌊y⌋) := by 
      have h11 : Real.sqrt (y - ⌊y⌋) ≥ 0 := Real.sqrt_nonneg (y - ⌊y⌋)
      linarith
    linarith [h11, h10]
  by_cases h2 : ⌊x⌋ = ⌊y⌋
  · -- case where `⌊x⌋ = ⌊y⌋`
    have h3 : ⌊x⌋ = ⌊y⌋ := h2
    have h4 : (⌊x⌋ : ℝ) = (⌊y⌋ : ℝ) := by 
      exact_mod_cast h3
    have h5 : (x - ⌊x⌋) < (y - ⌊y⌋) := by 
      have h6 : x < y := hxy
      have h7 : ⌊x⌋ = ⌊y⌋ := h3
      have h8 : (⌊x⌋ : ℝ) = (⌊y⌋ : ℝ) := by 
        exact_mod_cast h7
      nlinarith
    have h6 : Real.sqrt (x - ⌊x⌋) < Real.sqrt (y - ⌊y⌋) := by 
      apply Real.sqrt_lt_sqrt
      · -- Show 0 <= x - floor x 
        have h7 : x - ⌊x⌋ ≥ 0 := by
          have h31 : ⌊x⌋ ≤ x := Int.floor_le x
          linarith
        linarith
      · -- Show x - floor x < y - floor y 
        nlinarith
    linarith [h6, h4]
  · -- case where $\lfloor x \rfloor > \lfloor y \rfloor$, which is a contradiction
    have h3 : ⌊x⌋ > ⌊y⌋ := by 
      omega
    have h4 : (⌊x⌋ : ℝ) ≥ (⌊y⌋ : ℝ) + 1 := by 
      exact_mod_cast (show ⌊x⌋ ≥ ⌊y⌋ + 1 by omega)
    have h5 : (⌊y⌋ : ℝ) + 1 > y := by 
      have h6 : y < (⌊y⌋ + 1 : ℝ) := by
        exact Int.lt_floor_add_one y
      linarith
    have h10 : (⌊x⌋ : ℝ) > y := by
      nlinarith [h5, h4]
    have h11 : x ≤ y := by linarith
    have h12 : x ≥ (⌊x⌋ : ℝ) := by 
      have h13 : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
      linarith
    nlinarith