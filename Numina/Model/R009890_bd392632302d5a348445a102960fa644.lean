import Mathlib

theorem algebra_10757 (M T H A S : ℝ) (heq : M = T ∧ T = H) (hsum : M + T + H + A + S = 540) (hsupp : A + S = 180) :
    H = 120 := by 
  rcases heq with ⟨hm, hth⟩
  linarith [hm, hth, hsum, hsupp]