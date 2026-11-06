import Mathlib

/-
Proves that the difference between the sum of two geometric series 
(one representing squares and the other circles) equals (4 - π)/2
-/
theorem Geometry_608581
  (S T: ℕ → ℝ )
  (hS : ∀ i , S i = (1 / 2 : ℝ) ^ i)  -- Sequence S defined as powers of 1/2
  (hS_square:S_square = ∑' (n : ℕ), S n)  -- Sum of sequence S
  (hT :∀ i, T i = ((π : ℝ) / 4) * (1 / 2 : ℝ) ^ i)  -- Sequence T scaled by π/4
  (hT_square:T_square = ∑' (n : ℕ) , T n) :  -- Sum of sequence T
  S_square - T_square = (4 - π) / 2 := 
by

  -- Proves the sum of the geometric series ∑(1/2)ⁿ equals 2
  have h₁ : (∑' (n : ℕ), (1 / 2 : ℝ) ^ n) = 2 := by
    rw [tsum_geometric_two]

  -- Proves the sum of the scaled geometric series ∑(π/4)(1/2)ⁿ equals π/2
  have h₂ : (∑' (n : ℕ), ((π : ℝ) / 4 : ℝ) * (1 / 2 : ℝ) ^ n) = (π:ℝ) / 2 := by

    -- Factor out the constant π/4 from the summation
    have h₃ : (∑' (n : ℕ), ((π:ℝ) / 4 : ℝ) * (1 / 2 : ℝ) ^ n) = ((π:ℝ) / 4 : ℝ) * ∑' (n : ℕ), ((1 / 2 : ℝ) ^ n) := by
      rw [tsum_mul_left]
    rw [h₃]
    rw [tsum_geometric_two]
    ring 
  norm_cast 

  -- Substitute all known values into the original equation
  simp only [hS_square , hT_square , hS , hT , h₁ , h₂]
  field_simp 
  ring  