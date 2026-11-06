import Mathlib

def lucas (n : ℕ) : ℕ := match n with
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas n + lucas (n + 1)

/- The Lucas numbers $L_n$ are given by the recursion $L_0 = 2, L_1 = 1$, and $L_n = L_{n-1} + L_{n-2}$. Find the units digit of $L_{L_{10}}$. -/
theorem number_theory_16187 : lucas (lucas 10) % 10 = 4 := by
  simp [lucas]