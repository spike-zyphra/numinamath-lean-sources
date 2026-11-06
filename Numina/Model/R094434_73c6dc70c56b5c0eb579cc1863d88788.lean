import Mathlib

theorem algebra_265075 (a : ℕ) : 3^2 + 3^2 + 3^2 = 3^a ↔ a = 3 := by
  constructor
  · -- Forward direction: Assume 3^2 + 3^2 + 3^2 = 3^a, prove a = 3
    intro h
    have h1 : 3^2 + 3^2 + 3^2 = 3^3 := by
      norm_num
    -- So now h1 is 3^2+3^2+3^2 = 3^3 and h is 3^2+3^2+3^2 = 3^a, so transitivity gives 3^3 = 3^a
    have h2 : 3^3 = 3^a := by
      linarith
    -- Now use injectivity of the power function, if 3^3 = 3^a, then 3 = a
    have h3 : a = 3 := by
      exact Nat.pow_right_injective (by norm_num) h2.symm
    exact h3
  · -- Backward direction: Assume a = 3, prove 3^2 + 3^2 + 3^2 = 3^a
    intro h
    rw [h]
    -- The goal is now 3^2+3^2+3^2 = 3^3, which is true by calculation
    norm_num