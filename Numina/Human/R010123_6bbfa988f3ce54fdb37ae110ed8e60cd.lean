import Mathlib
/-Forty-eight congruent parallelograms with sides of length 62 feet and 20 feet are placed in a chevron pattern forming hexagon $ABCDEF$, as shown. What is the perimeter of hexagon $\allowbreak ABCDEF$?
-/
theorem algebra_3728 {n : ℕ} (hn : n = 48) :
    62 * 4 + 20 * n = 1208 := by 
  -- AB and DE consist of n segments each of length 20 feet. Each of BC,CD,EF,FA measure 62 feet.
  rw [hn]