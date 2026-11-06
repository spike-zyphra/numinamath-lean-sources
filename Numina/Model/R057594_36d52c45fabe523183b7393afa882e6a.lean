import Mathlib

theorem number_theory_118979 (O : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    {P | dist P O = r} = {P | P ∈ (Metric.sphere O r)} := by
  ext P
  simp [Metric.sphere]