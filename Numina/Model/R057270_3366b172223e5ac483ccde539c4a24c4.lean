import Mathlib

open Finset Real

theorem algebra_234578 {p : ℕ → ℝ} (hp : ∀ x, p x = x ^ 2 + 3 * x + 2) :
    ∏ i ∈ range 2022, (1 - 2 / p (i + 1)) = 675 / 2023 := by
  have hp2 : ∀ (x : ℕ), p x = (x : ℝ) ^ 2 + 3 * (x : ℝ) + 2 := by
    intro x
    specialize hp x
    exact_mod_cast hp
  norm_num [prod_range_succ, hp2]