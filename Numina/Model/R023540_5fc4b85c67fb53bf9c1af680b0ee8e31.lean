import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_7371
  (f : ℕ → ℝ)
  (h₀ : ∀ n, f n = sqrt (7 - f (n - 1)))
  (h₁ : f 0 = 0) :
  ∃ l, Tendsto f atTop (𝓝 l) ↔ l = 2 := by
  have h2 := h₀ 0
  have h3 : f 0 = sqrt (7 - f (0 - 1 : ℕ)) := by
    simpa using h2
  have h4 : f (0 - 1 : ℕ) = f 0 := by 
    simp 
  have h5 : f 0 = sqrt (7 - f 0) := by 
    rw [h4] at h3 
    linarith [h3] 
  have h6 : f 0 = (0 : ℝ) := h₁
  -- So from h5 and h6, we can conclude `0 = sqrt 7`.
  have h7 : (0 : ℝ) = sqrt (7 - (0 : ℝ)) := by 
    rw [h6] at h5 
    linarith [h5] 
  have h8 : sqrt (7 - (0 : ℝ)) = Real.sqrt 7 := by
    norm_num
  rw [h8] at h7
  have h9 : Real.sqrt 7 > 0 := by 
    apply Real.sqrt_pos.mpr
    all_goals linarith 
  have h11 : Real.sqrt 7 = (0 : ℝ) := by
    linarith [h7] 
  have h12 : (7 : ℝ) = (0 : ℝ) := by 
    calc
      (7 : ℝ) = (Real.sqrt 7) ^ 2 := by 
        rw [Real.sq_sqrt]
        all_goals linarith 
      _ = (0 : ℝ) ^ 2 := by 
        rw [h11] 
      _ = (0 : ℝ) := by 
        norm_num 
  nlinarith