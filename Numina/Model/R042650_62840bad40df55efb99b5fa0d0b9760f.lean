import Mathlib

open Topology Filter

theorem calculus_184908 (x : ℝ) :
    Tendsto (λ n => x^n / Nat.factorial n) atTop (𝓝 0) := by
  apply Real.tendsto_pow_div_factorial_atTop