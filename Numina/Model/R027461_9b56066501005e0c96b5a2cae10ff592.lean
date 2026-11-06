import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem calculus_310294 (q : ℝ) (hq : |q| < 1) :
    Tendsto (λ n => q ^ n) atTop (𝓝 0) := by
  apply tendsto_pow_atTop_nhds_zero_of_abs_lt_one
  exact hq