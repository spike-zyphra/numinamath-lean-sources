import Mathlib

open Real

theorem other_5302 {K : ℝ} (hK : K ∈ Set.Icc 0 100) (m : ℝ) (hm : m = 2)
    (A B : ℝ) (hA : A ∈ Set.Ioo 0 (π / 2)) (hB : B ∈ Set.Ioo 0 (π / 2))
    (hAB : A = B - π / 2) :
    m = 2 := by
  exact hm