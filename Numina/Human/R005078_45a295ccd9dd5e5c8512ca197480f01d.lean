import Mathlib

open Finset

/-
A $9 \times 7$ rectangle is tiled with pieces of two types, shown in the picture below. Find the possible values of the number of the $2 \times 2$ pieces which can be used in such a tiling.
-/
theorem combinatorics_605392 
    (x y : ℕ) 
    (hx : x + y ≥ 20) 
    (hy : 3 * x + 4 * y = 63) :
    y = 0 ∨ y = 3 := by

  -- Bounding y: Subtract the inequality 3*(x + y) ≥ 60 (derived from x + y ≥ 20) from the equation 3x + 4y = 63. This gives (3x + 4y) - 3(x + y) = 63 - 60 ⇒ y ≤ 3.
  have h₁ : y ≤ 3 := by
    omega

  -- Modular Arithmetic: From the equation 3x + 4y = 63, note that 3x + 4y ≡ 0 mod 3. Since 3x ≡ 0 mod 3, we have 4y ≡ y ≡ 0 mod 3. Thus, y must be a multiple of 3.
  have h₂ : y % 3 = 0 := by
    omega

  -- Deducing Possible Values of y: Combine the results y ≤ 3 and y ≡ 0 mod 3. The natural numbers satisfying both conditions are y = 0 and y = 3.
  have h₃ : y = 0 ∨ y = 3 := by
    have h₄ : y ≤ 3 := h₁
    have h₅ : y % 3 = 0 := h₂

    -- Case analysis for y in the interval [0, 3]
    interval_cases y 
    
    -- Verify modular condition for each case
    norm_num at h₅
    
    -- Discharge each case using arithmetic reasoning
    all_goals omega 

  exact h₃