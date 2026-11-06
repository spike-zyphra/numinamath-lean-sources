import Mathlib

/- Show that the equation

$$
x^{2}+y^{2}+z^{2}=(x-y)(y-z)(z-x)
$$

has infinitely many solutions in integers $x, y, z$. -/
theorem algebra_607792 :
  { (x, y, z) : ℤ × ℤ × ℤ | x ^ 2 + y ^ 2 + z ^ 2 = (x - y) * (y - z) * (z - x) }.Infinite := by
  -- We can show that for any n ∈ ℕ, the triple ((2n-1)(6n^2+1), 2n(6n^2+1), (2n+1)(6n^2+1)) is a solution.
  -- We set f : ℕ → ℤ × ℤ × ℤ to be this map.
  let f (n : ℕ) : ℤ × ℤ × ℤ := ((2 * n - 1) * (6 * n ^ 2 + 1), 2 * n * (6 * n ^ 2 + 1), (2 * n + 1) * (6 * n ^ 2 + 1))
  -- It suffices to show that f is injective, and that f(n) is a solution for all n ∈ ℕ.
  apply Set.infinite_of_injective_forall_mem (f := f)
  . -- We take the third coordinate of f and show it is strictly monotone.
    let f3 (n : ℕ) : ℤ := (2 * n + 1) * (6 * n ^ 2 + 1)
    have hf3 : StrictMono f3 := by
      intro n m h
      simp [f3]
      norm_cast
      -- 2 * n + 1 < 2 * m + 1
      -- 6 * n ^ 2 + 1 < 6 * m ^ 2 + 1
      apply Nat.mul_lt_mul_of_lt_of_lt
      . simp [h]
      . simp
        refine Nat.pow_lt_pow_left h (by simp)
    -- Thus the third coordinate of f is injective.
    -- And so is f.
    apply StrictMono.injective at hf3
    intro n m h
    simp [f] at h
    exact hf3 h.2.2
  . -- We show that f(n) is a solution for all n ∈ ℕ.
    intro n
    simp [f]
    -- It is an identity in ring.
    ring
