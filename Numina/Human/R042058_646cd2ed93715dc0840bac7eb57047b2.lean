import Mathlib

/- 3. Misha calculated the products $1 \times 2, 2 \times 3$, $3 \times 4, \ldots, 2017 \times 2018$. For how many of them is the last digit zero? -/
theorem number_theory_144645 : {i ∈ Finset.Icc 1 2017 | (i * (i + 1)) % 10 = 0}.card = 806 := by
  native_decide