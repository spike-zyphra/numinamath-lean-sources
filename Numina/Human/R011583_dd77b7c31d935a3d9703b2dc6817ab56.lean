import Mathlib

def dot (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2
def mul_left (u : ℝ) (v : ℝ × ℝ) : ℝ × ℝ := (u * v.1, u * v.2)
def mul_right (u : ℝ × ℝ) (v : ℝ) : ℝ × ℝ := (u.1 * v, u.2 * v)

/- a,b,c are three non-zero vectors, m∈ℝ, show that (a · b) * c = a * (b · c) is incorrect. -/
theorem algebra_272513 : ∃ a b c : ℝ × ℝ, mul_left (dot a b) c ≠ mul_right a (dot b c) := by
  use (1,2), (2,3), (3,4)
  rw [dot, mul_left, mul_right, dot]
  ring_nf
  simp
