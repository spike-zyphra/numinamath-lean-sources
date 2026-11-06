import Mathlib

/- Fibonacci sequence -/
def u1 : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => u1 n + u1 (n + 1)

/- Show that if \( n \) is a positive integer, then \( u_{n+1} u_{n-1} - u_{n}^{2} = (-1)^{n} \). -/
theorem number_theory_4543 {n} (hn : n > 0) : u1 (n + 1) * u1 (n - 1) - u1 n ^ 2 = (-1) ^ n :=
  -- This is an inductive proof
  match n with
  -- check base case n=0
  | 0 => by simp at hn
  -- check base case n=1
  | 1 => rfl
  | n + 2 => by
    simp only [u1, Nat.add_one_sub_one, Int.reduceNeg]
    ring_nf
    -- after using induction hypothesis we can deduce by simple calculation
    rw [add_comm 1 n,
      show u1 (n + 1) ^ 2 = u1 (n + 2) * u1 n - (-1) ^ (n + 1) by
        rw [← number_theory_4543 (by linarith)]; simp]
    simp only [u1]
    ring
