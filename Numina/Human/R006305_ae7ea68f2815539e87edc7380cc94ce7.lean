import Mathlib

/- Let $N$ be a positive integer. Determine the number of invertible elements in the monoid $(\mathbb{Z}_N, \cdot)$, where $\mathbb{Z}_N$ denotes the ring of integers modulo $N$ and $\cdot$ denotes multiplication modulo $N$. Show that this number is equal to $\phi(N)$, where $\phi$ is Euler's totient function. -/
theorem number_theory_635700 (N : ℕ) [NeZero N] :
    Fintype.card (ZMod N)ˣ = N.totient := by
  -- ZMod N is the elements of ℤ modulo N
  -- (ZMod N)ˣ is the elements of ZMod N that are invertible
  -- It is a library lemma that the number of invertible elements in ZMod N is equal to the totient of N
  exact ZMod.card_units_eq_totient _