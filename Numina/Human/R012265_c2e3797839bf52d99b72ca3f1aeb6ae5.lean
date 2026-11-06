import Mathlib

open Nat

/- Let x and y be two-digit positive integers with mean 60. 
What is the maximum value of the ratio x / y? 
(A) 3 (B) 33/7 ​(C) 39/7​ (D) 9 (E) 99/10
-/
theorem algebra_94980 (x y : ℕ) (hx : x ∈ Finset.Icc 10 99) (hy : y ∈ Finset.Icc 10 99)
(hxy : (x + y) = 2 * 60) :
(x / y : ℚ) ≤ 33 / 7 := by
  simp at hxy
  -- `x` is no more than `99`, so `y` is at least `21`
  have h : x ≤ 99 := ((LocallyFiniteOrder.finset_mem_Icc 10 99 x).1 hx).2
  have h₂ : x + y ≤ 99 + y := add_le_add_right h y
  rw [hxy] at h₂
  have h₃ : 21 ≤ y := le_of_add_le_add_left h₂
  -- therefore, `x / y` is no more than `99 / 21 = 33 / 7`.
  -- first, show `x / y < 99 / y`
  have h₄ : (x / y : ℚ) ≤ 99 / y :=
    (div_le_div_iff_of_pos_right (cast_pos'.mpr (zero_lt_of_lt h₃))).mpr (cast_le_ofNat.mpr h)
  -- then, show `99 / y ≤ 99 / 21`
  have h₅ : (99 / y : ℚ) ≤ 99 / 21 :=
    (div_le_div_iff_of_pos_left rfl (cast_pos'.mpr (zero_lt_of_lt h₃)) rfl).mpr (ofNat_le_cast.mpr h₃)
  have h₆ : (99 / 21 : ℚ) = 33 / 7 := by norm_num
  rw [← h₆]
  -- finally, combine these facts
  exact h₄.trans h₅