import Mathlib

/- Solve the system of equations: $\left\{\begin{array}{l}{2x+3y=7}\\{x=-2y+3}\end{array}\right.$. -/
theorem algebra_9457 {x y : ℝ} (h1 : 2 * x + 3 * y = 7) (h2 : x = -2 * y + 3) : x = 5 ∧ y = -1 := by
  have yeq: y = -1 := by
  -- substitue equation h2 into equation h1, and we can solve y=-1.
    rw [h2] at h1
    have:  2 * (-2 * y + 3) + 3 * y = 6-y := by ring
    rw [this] at h1
    have ht1: 6 - y + y = 7 + y := by rw [h1]
    have ht2: 6 - y + y = 6 := by ring
    rw [ht2] at ht1
    have ht3: -7+6 = -7+7+y := by
      rw [ht1]
      ring
    simp at ht3
    rw [← ht3]
    norm_num
  have xeq: x = 5 := by
    -- substitue y = -1 back into equation h2, we cna get x=5
    rw [yeq] at h2
    rw [h2]
    norm_num
  exact ⟨xeq,yeq⟩