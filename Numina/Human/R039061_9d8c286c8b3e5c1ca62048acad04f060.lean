import Mathlib

open Real Set
open scoped BigOperators

/--
Which of the following describes the largest subset of values of `y` within the closed interval `[0, π]`
for which `sin(x + y) ≤ sin(x) + sin(y)` for every `x` in `[0, π]`, inclusive?

(A) `y = 0`
(B) `0 ≤ y ≤ π/4`
(C) `0 ≤ y ≤ π/2`
(D) `0 ≤ y ≤ 3π/4`
(E) `0 ≤ y ≤ π`
-/

theorem inequalities_98082 (y : ℝ) (hy : y ∈ Icc 0 π) :
  (∀ x ∈ Icc 0 π, sin (x + y) ≤ sin x + sin y) ↔ y ∈ Icc 0 π := by
    -- We'll prove an "if and only if" statement in two directions:
  apply Iff.intro 
    -- (→) direction: If sin(x+y) ≤ sin x + sin y for all x ∈ [0, π], then y must be in [0, π]. But we already have `hy`, so it's trivial.
  { intro _
    exact hy }
    -- (←) direction: If y ∈ [0, π], then for all x ∈ [0, π], we have sin(x + y) ≤ sin x + sin y.
  { intro _
    intro x hx
    -- Expand sin(x+y)
    rw [sin_add]
    -- We need: sin x * cos y + cos x * sin y ≤ sin x + sin y
    apply add_le_add
    -- Part 1: we show sin x * cos y ≤ sin x
    { calc
        sin x * cos y
          ≤ sin x * 1 := by
            apply mul_le_mul_of_nonneg_left
    -- Also, cos y ≤ 1 for y ∈ [0, π]
            · exact cos_le_one y         
    -- Finally, sin x ≥ 0 for x ∈ [0, π]
            · exact sin_nonneg_of_mem_Icc hx  
        _ = sin x := by rw [mul_one (sin x)] }
    -- Part 2: We infer cos x * sin y ≤ sin y
    { calc
        cos x * sin y
          ≤ 1 * sin y := by
            apply mul_le_mul_of_nonneg_right
    -- Also cos x ≤ 1 for x ∈ [0, π]        
            · exact cos_le_one x       
    -- Consequently, sin y ≥ 0 for y ∈ [0, π]          
            · exact sin_nonneg_of_mem_Icc hy  
        _ = sin y := by rw [one_mul (sin y)] } }