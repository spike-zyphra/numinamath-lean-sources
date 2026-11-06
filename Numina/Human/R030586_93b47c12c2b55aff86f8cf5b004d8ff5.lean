import Mathlib

theorem algebra_21272 : IsGreatest {z : ℝ | ∃(x y : ℝ), |x + y| + |x - y| = 2 ∧ z = x^2 - 6 * x + y^2} 8 := by
  constructor
  · -- Prove that 8 is in the set.
    use -1
    use -1
    norm_num
  · -- Prove that any element in the set is less than or equal to 8.
    apply mem_upperBounds.mpr
    simp
    intro z x y hxy hz
    rw [hz]
    -- First, we find the graph of $|x + y| + |x - y| = 2$ in the coordinate plane.
    obtain (⟨hr₁, hr₂⟩ | ⟨hr₁, hr₂⟩) := abs_cases (x + y)
    · -- |x + y| = x + y
      obtain (⟨hx₁, hx₂⟩ | ⟨hy₁, hy₂⟩) := abs_cases (x - y)
      · -- |x - y| = x - y
        -- If $y \le x,$ then
        -- \[|x + y| + |x - y| = x + y + x - y = 2,\]so $x = 1.$  Thus, the graph of in the first quadrant consists of the line segment connecting $(1,0)$ to $(1,1),$ and the line segment connecting $(0,1)$ to $(1,1).$
        rw [hx₁, hr₁] at hxy
        have : x = 1 := by linarith
        rw [this]
        have : y^2 ≤ 1 := by
          rw [Real.sq_le]
          simp
          constructor
          all_goals linarith
        linarith
      · -- |x - y| = y - x
        -- we consider the case where $x \ge 0$ and $y \ge 0.$  If $y \ge x,$ then
        -- \[|x + y| + |x - y| = x + y + y - x = 2,\]so $y = 1.$
        rw [hy₁, hr₁] at hxy
        have : y = 1 := by linarith
        rw [this]
        have : x^2 ≤ 1 := by
          rw [Real.sq_le]
          simp
          constructor
          all_goals linarith
        linarith
    · -- |x + y| = -(x + y)
      obtain (⟨hx₁, hx₂⟩ | ⟨hy₁, hy₂⟩) := abs_cases (x - y)
      · -- |x - y| = x - y
        rw [hr₁, hx₁] at hxy
        have : y = -1 := by linarith
        rw [this]
        simp
        have : x^2 ≤ 1 := by
          rw [Real.sq_le]
          simp
          constructor
          all_goals linarith
        linarith
      · -- |x - y| = y - x
        rw [hr₁, hy₁] at hxy
        have : x = -1 := by linarith
        rw [this]
        simp
        have : y^2 ≤ 1 := by
          rw [Real.sq_le]
          simp
          constructor
          all_goals linarith
        linarith
