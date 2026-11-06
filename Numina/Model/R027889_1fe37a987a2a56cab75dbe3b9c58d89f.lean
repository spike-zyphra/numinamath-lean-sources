import Mathlib

open Real Set
open scoped Real

theorem algebra_13717 {x : ℝ} :
  tan x + cos x * sin x - tan x * cos x ^ 2 = tan x := by
  have htan : tan x = sin x / cos x := by
    rw [tan_eq_sin_div_cos]
  rw [htan]
  by_cases h : cos x = 0
  · -- If cos x = 0 then both sides are 0/0 and thus equal
    rw [h]
    norm_num
  · -- Case cos x ≠ 0.
    have hc : cos x ≠ 0 := h
    field_simp [hc]
    <;> ring