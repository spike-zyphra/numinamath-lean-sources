import Mathlib

/- Fibonacci sequence -/
def u2 : ℕ → ℝ
| 0 => 0
| 1 => 1
| n + 2 => u2 n + u2 (n + 1)

/- Definition of constant `α` and `β`. -/
noncomputable def α := (1 + √5) / 2
noncomputable def β := (1 - √5) / 2

theorem number_theory_4544 (n) : u2 n = (α ^ n - β ^ n) / √5 :=
  -- This is an inductive proof
  match n with
  -- check base case n=0
  | 0 => by simp [u2]
  -- check base case n=1
  | 1 => by simp [u2, α, β]
  | n + 2 => by
    simp [u2, number_theory_4544, α, β]
    -- using the following facts, we can draw a conclusion by simple calculation:
    -- `√5^2=5`, `√5^3=5√5`, `√5^4=25`
    have pow_2 : √5 ^ 2 = 5 := by simp
    have pow_3 : √5 ^ 3 = 5 * √5 := by simp [pow_succ]
    have pow_4 : √5 ^ 4 = 25 := by
      rw [show 4 = 2 + 2 by simp, pow_add, pow_2]
      norm_num
    field_simp
    ring_nf
    simp only [pow_2, pow_3, pow_4]
    ring
