import Mathlib

open Finset Real

theorem algebra_135491 {f : ℝ → ℝ → ℝ} (hf : ∀ a b, f a b = (a * b + 1) / (a + b)) :
    f 1 (f 2 (f 3 (f 2017 2018))) = 1 := by
  have h1 : f 2017 2018 = (2017 * 2018 + 1) / (2017 + 2018) := hf 2017 2018
  have h2 : f 3 (f 2017 2018) = (3 * (f 2017 2018) + 1) / (3 + (f 2017 2018)) := by 
    apply hf 
  have h3 : f 2 (f 3 (f 2017 2018)) = (2 * (f 3 (f 2017 2018)) + 1) / (2 + (f 3 (f 2017 2018))) := by 
    apply hf 
  have h4 : f 1 (f 2 (f 3 (f 2017 2018))) = (1 * (f 2 (f 3 (f 2017 2018))) + 1) / (1 + (f 2 (f 3 (f 2017 2018))) ) := by 
    apply hf 
  rw [h4, h3, h2, h1]
  norm_num