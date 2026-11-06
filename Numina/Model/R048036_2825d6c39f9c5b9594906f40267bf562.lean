import Mathlib

def M (u : ℤ) := ∃ m n l, u = 12 * m + 8 * n + 4 * l
def N (u : ℤ) := ∃ p q r, u = 20 * p + 16 * q + 12 * r

theorem number_theory_126892 :
    {u | M u} = {u | N u} := by 
  ext u
  simp [M, N]
  constructor
  · -- Assume $u \in M$, we need to show $u \in N$.
    rintro ⟨m, n, l, h⟩
    refine ⟨n + l, -l, m - n, ?_⟩
    linarith
  · -- Assume $u \in N$, we need to show $u \in M$.
    rintro ⟨p, q, r, h⟩
    refine ⟨p, q, 2 * p + 2 * q + 3 * r, ?_⟩
    linarith