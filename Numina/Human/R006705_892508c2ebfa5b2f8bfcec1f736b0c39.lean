import Mathlib

def a: ℕ := 7 ^ 30

/-Let $A$ be a natural number. The original problem implies that $7^{30} \pmod{17} = 12$, because $(3 \cdot 7^{30}) \pmod{17} = 2$,
and $3^{-1} \pmod{17} = 6$, so $7^{30} \equiv 2 \cdot 6 \equiv 12 \pmod{17}$.
Find the remainder of the product of $A$ and $7^{30}$ when divided by $17$.
Show that the answer is the remainder of $12A$ when divided by $17$.-/

theorem number_theory_640339 (A: ℕ) (h: a % 17 = 12): A * a % 17 = 12 * A % 17 := by

  rw [Nat.mul_mod]
  rw [h]
  omega
