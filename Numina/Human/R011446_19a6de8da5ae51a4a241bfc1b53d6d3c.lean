import Mathlib

/- Example 2 The set $M=\{u \mid u=12 m+8 n+4 l, m, n, l \in \mathbf{Z}\}$ and

$$

N=\{u \mid u=20 p+16 q+12 r, p, q, r \in \mathbf{Z}\}

$$


The relationship between them is ( ).
A. $M=N$
B. $M \not \subset N$ and $N \not \subset M$
C. $M \subset N$
D. $M \supset N$ -/
theorem number_theory_246917 :
    {x : ℤ | ∃ m n l : ℤ, x = 12 * m + 8 * n + 4 * l} =
    {x : ℤ | ∃ p q r : ℤ, x = 20 * p + 16 * q + 12 * r} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · rintro ⟨m, n, l, h⟩
    --Use witnesses.
    use (3 * m + 2 * n + l)
    use (- (3 * m + 2 * n + l))
    use 0
    linarith
  · rintro ⟨p, q, r, h⟩
    --Use witnesses
    use (5 * p + 4 * q + 3 * r)
    use (- (5 * p + 4 * q + 3 * r))
    use 0
    linarith