import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

theorem algebra_146910 {z : ℕ → ℂ} (hz : ∀ n, z n ≠ 0)
    (hzz : ∀ m n, m ≠ n → ‖z m - z n‖ > 1) :
    ∃ y, y = ∑' n : ℕ, 1/(z n)^3 :=
  by
  let y := ∑' n : ℕ, 1 / (z n) ^ 3
  use y
  done