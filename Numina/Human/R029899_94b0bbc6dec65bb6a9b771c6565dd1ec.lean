import Mathlib

/- A composite positive integer is a product $ab$ with $a$ and $b$ not necessarily distinct integers in $\{2,3,4,\dots\}$. Show that every composite positive integer is expressible as $xy+xz+yz+1$, with $x,y,z$ positive integers. -/
theorem number_theory_74692 {n : ℕ} (hn : ∃ a b, n = a * b ∧ a > 1 ∧ b > 1) :
    ∃ x y z, n = x * y + x * z + y * z + 1 ∧ x > 0 ∧ y > 0 ∧ z > 0 := by
  obtain ⟨a, b, hn⟩ := hn
  use a - 1, b - 1, 1
  cases' a with a
  · simp_all
  cases' b with b
  · simp_all
  simp_all [Nat.succ_mul, Nat.mul_succ]
  <;> omega