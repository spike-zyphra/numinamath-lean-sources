import Mathlib

theorem algebra_93273 (x y z : ℤ) (h : x = z ∧ y - 1 = x) :
x * (x - y) + y * (y - z) + z * (z - x) = 1 := by
  rcases h with ⟨h1, h2⟩
  have hy : y = x + 1 := by omega
  have hz : z = x := by linarith
  rw [hy, hz]
  ring