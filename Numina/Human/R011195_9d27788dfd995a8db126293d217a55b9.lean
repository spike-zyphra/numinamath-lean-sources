import Mathlib

/- Find the smallest integer $n$ such that $\sqrt{n+99}-\sqrt{n}<1$. -/
theorem number_theory_611248 :
    IsLeast {n : ℕ | √(n + 99) - √n < 1} 2402 := by
  -- It suffices to show that the inequality is equivalent to 2401 < n.
  suffices H : ∀ n : ℕ, √(n + 99) - √n < 1 ↔ 2401 < n by
    simp [H]
    exact isLeast_Ici
  intro n
  calc √(n + 99) - √n < 1
    -- Move the term
    _ ↔ √(n + 99) < √n + 1 := sub_lt_iff_lt_add'
    -- Square both sides
    _ ↔ n + 99 < (√n + 1) ^ 2 := Real.sqrt_lt' (by positivity)
    -- Expand the right-hand side
    _ ↔ n + 99 < n + 2 * √n + 1 := by
      simp [← sub_pos]
      ring_nf
      simp
    -- Cancel the term
    _ ↔ 99 < 2 * √n + 1 := by rw [add_assoc]; simp
    -- Simplify the inequality
    _ ↔ 49 < √n := by constructor <;> intro h <;> linarith
    -- Square both sides
    _ ↔ 49 ^ 2 < (n : ℝ) := Real.lt_sqrt (by simp)
    -- Simplify the inequality
    _ ↔ 2401 < n := by norm_num
