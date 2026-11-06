import Mathlib

theorem algebra_224866 (x : ℝ) (hx : x ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2)) (h : (Real.tan x)^5 - (Real.tan x)^3 + (Real.tan x) = 2) :
    3 < (Real.tan x)^6 ∧ (Real.tan x)^6 < 4 := by
  rcases hx with ⟨hx1, hx2⟩
  constructor
  · -- Prove that 3 < (Real.tan x) ^ 6
    nlinarith [sq_nonneg (Real.tan x ^ 2 - 1), sq_nonneg (Real.tan x ^ 2 - Real.tan x), sq_nonneg (Real.tan x - 1), sq_nonneg (Real.tan x ^ 2 - 1), sq_nonneg (Real.tan x ^ 2 - Real.tan x + 1), sq_nonneg (Real.tan x ^ 2 - 1), sq_nonneg (Real.tan x - 1)]
  · -- Prove that (Real.tan x) ^ 6 < 4
    nlinarith [sq_nonneg (Real.tan x ^ 2 - 1), sq_nonneg (Real.tan x ^ 2 - Real.tan x), sq_nonneg (Real.tan x - 1), sq_nonneg (Real.tan x ^ 2 - 1), sq_nonneg (Real.tan x ^ 2 - Real.tan x + 1), sq_nonneg (Real.tan x ^ 2 - 1), sq_nonneg (Real.tan x - 1)]