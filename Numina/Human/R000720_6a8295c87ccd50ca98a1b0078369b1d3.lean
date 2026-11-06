import Mathlib

/-In Chemistry class, Samantha finds that she can make a certain solution by mixing $.04$ liters of chemical A with $.02$ liters of water (this gives her $.06$ liters of the solution). She wants to make a total of $.48$ liters of this new solution.  To do so, how many liters of water will she use?-/
theorem algebra_14267 {ratio_of_A_to_total ratio_of_A_to_water total ratio_of_water_to_total: ℝ} (h : ratio_of_A_to_water = 0.02/0.04) (h₂: total = 0.48) (h₃: ratio_of_A_to_total = ratio_of_A_to_water / (1 + ratio_of_A_to_water)) (h₄ : ratio_of_water_to_total = ratio_of_A_to_total / ratio_of_A_to_water) : total * ratio_of_water_to_total = 0.32 := by
  -- Firstly, we find that $\frac{.02}{.06}=\frac{1}{3}$ is the fraction of water in the solution.  Thus, since Samantha wants $.48$ total liters of the solution, we have that she must use $.48 \times \frac{1}{3}=\boxed{0.16}$ liters of water.
  rw [h₄, h₃, h, h₂]
  ring_nf
