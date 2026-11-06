import Mathlib

def dot (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2
def mul_left (u : ℝ) (v : ℝ × ℝ) : ℝ × ℝ := (u * v.1, u * v.2)
def mul_right (u : ℝ × ℝ) (v : ℝ) : ℝ × ℝ := (u.1 * v, u.2 * v)

theorem algebra_272513 : ∃ a b c : ℝ × ℝ, mul_left (dot a b) c ≠ mul_right a (dot b c) := by
  use (1, 2)
  use (3, 4)
  use (5, 6)
  simp [dot, mul_left, mul_right]
  all_goals
    norm_num
    <;> try { tauto }