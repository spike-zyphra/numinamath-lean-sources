import Mathlib
/- For the sequence of numbers $n_{1}, n_{2}, n_{3}, \ldots$, the relation $n_{i}=2 n_{i-1}+a$ holds for all $i>1$. If $n_{2}=5$ and $n_{8}=257$, what is $n_{5}$ ? -/
theorem algebra_610936 (n : ℕ → ℝ) (hn : ∀ i > 0, n (i + 1) = 2 * n i + a) (h2 : n 2 = 5) (h8 : n 8 = 257) : n 5 = 33 := by
  -- Apply the sequence relation for i = 2
  have g1:= hn 2 (by omega)
  -- Apply the sequence relation for i = 3
  have g2:= hn 3 (by omega)
  -- Apply the sequence relation for i = 4
  have g3:= hn 4 (by omega)
  -- Apply the sequence relation for i = 5
  have g4:= hn 5 (by omega)
  -- Apply the sequence relation for i = 6
  have g5:= hn 6 (by omega)
  -- Apply the sequence relation for i = 7
  have g6:= hn 7 (by omega)
  -- Simplify all equations using ring normalization
  ring_nf at g1 g2 g3 g4 g5 g6
  -- Solve the system of equations using linear arithmetic
  linarith
