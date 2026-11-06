import Mathlib

/-
John has a 1 liter bottle of pure orange juice. He pours half of the contents of the bottle into a vat, fills the bottle with water, and mixes thoroughly. He then repeats this process 9 more times. Afterwards, he pours the remaining contents of the bottle into the vat. What fraction of the liquid in the vat is now water?
-/
theorem algebra_609811  (orange water : ℝ) (ho: orange = 1) (times : ℕ) (htimes : times = 10) (hw: water = times / 2) : water / (water + orange) = 5/6 := by

  have : (times: ℝ) = 10 := by norm_cast
  rw [this] at hw
  norm_num at hw
  rw [hw, ho]
  norm_num
  