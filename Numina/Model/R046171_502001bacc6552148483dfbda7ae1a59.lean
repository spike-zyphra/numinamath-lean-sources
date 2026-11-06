import Mathlib
theorem algebra_604443 : {(x, y, z) : ℝ × ℝ × ℝ | x ^ 2 + y ^ 2 + z ^ 2 + 1 = x * y + y * z + z * x + |x - 2 * y + z|} =
{(x, y, z) : ℝ × ℝ × ℝ | ∃ t : ℝ, (x, y, z) = (t + 1, t, t + 1) ∨ (x, y, z) = (t - 1, t, t - 1)}:= by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- Assume (x, y, z) satisfies the equation.
    intro h
    by_cases h1 : x - 2 * y + z ≥ 0
    · -- If x - 2y + z ≥ 0, then |x - 2y + z| = x - 2y + z.
      rw [abs_of_nonneg h1] at h
      have h2 : (x - (y + 1)) ^ 2 + (z - (y + 1)) ^ 2 = 0 := by
        nlinarith
      have hx1 : x = y + 1 := by
        nlinarith
      have hz1 : z = y + 1 := by
        nlinarith
      use y
      left
      simp [hx1, hz1]
    · -- If x - 2y + z < 0, then |x - 2y + z| = -(x - 2y + z).
      rw [abs_of_neg (lt_of_not_ge h1) ] at h
      have h2 : (x - (y - 1)) ^ 2 + (z - (y - 1)) ^ 2 = 0 := by
        nlinarith
      have hx1 : x = y - 1 := by
        nlinarith
      have hz1 : z = y - 1 := by
        nlinarith
      use y
      right
      simp [hx1, hz1]
  · -- Assume (x, y, z) is of the form (t + 1, t, t + 1) or (t - 1, t, t - 1).
    rintro ⟨t, h1⟩
    rcases h1 with h1 | h1
    · -- Case (t + 1, t, t + 1).
      rw [h1.1, h1.2.1, h1.2.2]
      have h2 : abs ((t + 1 : ℝ) - 2 * (t : ℝ) + (t + 1 : ℝ)) = 2 := by
        have h3 : (t + 1 : ℝ) - 2 * (t : ℝ) + (t + 1 : ℝ) = 2 := by
          ring
        rw [h3]
        norm_num
      rw [h2]
      nlinarith
    · -- Case (t - 1, t, t - 1).
      rw [h1.1, h1.2.1, h1.2.2]
      have h2 : abs ((t - 1 : ℝ) - 2 * (t : ℝ) + (t - 1 : ℝ)) = 2 := by
        have h3 : (t - 1 : ℝ) - 2 * (t : ℝ) + (t - 1 : ℝ) = -2 := by
          ring
        rw [h3]
        norm_num
      rw [h2]
      nlinarith