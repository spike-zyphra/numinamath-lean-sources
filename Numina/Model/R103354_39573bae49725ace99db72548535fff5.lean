import Mathlib

def θ (a b : ℕ) := a ^ b - b ^ a

theorem algebra_290457 {x y : ℕ} (hx : x = 2) (hy : y = 5) :
    θ x (θ 2 y) = 79 := by
  rw [hx, hy]
  norm_num [θ]