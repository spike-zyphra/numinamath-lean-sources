import Mathlib

/-Sharon bought a mixture of nuts that was made up of pecans, walnuts and cashews in a ratio by weight of $2:3:1$, respectively. If she bought $9$ pounds of nuts, how many pounds of walnuts were in the mixture? Express your answer as a decimal to the nearest tenth.-/
theorem algebra_18777 {x y z : ℝ} (_ : x > 0 ∧ y > 0 ∧ z > 0)
    (h1 : x * 3 = y * 2) (h2 : x * 1 = z * 2) (h3 : x + y + z = 9) :
    y = 4.5 := by
  suffices (4.5 : ℝ) = 9 /2 by rw [this]; linarith
  norm_num
