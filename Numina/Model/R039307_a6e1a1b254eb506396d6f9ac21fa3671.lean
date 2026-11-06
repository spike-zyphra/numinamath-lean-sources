import Mathlib

theorem algebra_20807 {f : ℝ → ℝ → ℝ → ℝ} (hf : f = λ x y z => 2 * x ^ 2 + 2 * y ^ 2 + 5 * z ^ 2 - 2 * x * y - 4 * y * z - 4 * x - 2 * z + 15) :
    IsLeast {r : ℝ | ∃ x y z, f x y z = r} 10 := by
  constructor
  · -- Show that 10 is in the set, using the critical point (2, 2, 1).
    use 2, 2, 1
    rw [hf]
    norm_num
  · -- Show that 10 is the least value in the set.
    intro r hr
    rcases hr with ⟨x, y, z, hre⟩
    rw [hf] at hre
    simp at hre
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 1),
              sq_nonneg (2 * x - y - 2), sq_nonneg (2 * y - 4 * z), sq_nonneg (x - 2 * y + 2)]