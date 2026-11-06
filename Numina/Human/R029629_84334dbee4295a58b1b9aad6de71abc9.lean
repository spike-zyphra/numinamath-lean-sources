import Mathlib

theorem algebra_224866 (x : ℝ) (hx : x ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2)) (h : (Real.tan x)^5 - (Real.tan x)^3 + (Real.tan x) = 2) :
    3 < (Real.tan x)^6 ∧ (Real.tan x)^6 < 4 := by 
  let t:= Real.tan x
  simp at *
  constructor
  . -- First, we show that $3 < t^6$.
    nlinarith [sq_nonneg (t^2 - 1), sq_nonneg (t - 1), sq_nonneg (t^2 + t/2 + 1/2), sq_nonneg (t^2 - t/2 + 1/2)]
  . -- Then, we show that $t^6 < 4$.
    nlinarith [sq_nonneg (t^2 - 1), sq_nonneg (t - 1), sq_nonneg (t^2 + t/2 + 1/2), sq_nonneg (t^2 - t/2 + 1/2)]