import Mathlib

/- Show that if \( a \) and \( b \) are positive real numbers, then \( \lfloor ab \rfloor \geq \lfloor a \rfloor \lfloor b \rfloor \).-/
theorem number_theory_4835_1 (a b : ℝ) {_ : a > 0} {_ : b > 0} {_ : a > 0 ∧ b > 0}
    : ⌊a * b⌋ ≥ ⌊a⌋ * ⌊b⌋ := by
  -- ⌊a⌋ ≤ a
  have le_a := Int.floor_le a
  -- ⌊b⌋ ≤ b
  have le_b := Int.floor_le b
  -- multiple `⌊a⌋ ≤ a` and `⌊b⌋ ≤ b` we have `⌊a⌋⌊b⌋ ≤ ab`
  have := mul_le_mul le_a le_b (by simp [Int.floor_nonneg]; linarith) (by linarith)
  -- as `⌊a⌋⌊b⌋` is integer, we can deduce that `⌊a⌋⌊b⌋ ≤ ⌊ab⌋`
  rw [←Int.cast_mul, ←Int.le_floor] at this
  apply this

/- What is the corresponding inequality when both \( a \) and \( b \) are negative? When one is negative and the other positive?-/
theorem number_theory_4835_2 (a b : ℝ) {_ : a > 0} {_ : b > 0} {_ : a < 0 ∧ b < 0}
    : ⌊a * b⌋ ≥ ⌊a⌋ * ⌊b⌋ := by
  -- ⌊a⌋ ≤ a
  have le_a := Int.floor_le a
  -- ⌊b⌋ ≤ b
  have le_b := Int.floor_le b
  -- multiple `⌊a⌋ ≤ a` and `⌊b⌋ ≤ b` we have `⌊a⌋⌊b⌋ ≤ ab`
  have := mul_le_mul le_a le_b (by simp [Int.floor_nonneg]; linarith) (by linarith)
  -- as `⌊a⌋⌊b⌋` is integer, we can deduce that `⌊a⌋⌊b⌋ ≤ ⌊ab⌋`
  rw [←Int.cast_mul, ←Int.le_floor] at this
  apply this
