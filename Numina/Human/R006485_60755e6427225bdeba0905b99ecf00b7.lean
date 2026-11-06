import Mathlib

open Matrix

def U (k : ℤ) := !![k, 1; 1, 0]

def g (k : ℤ) : ℕ → ℤ
| 0 => 0
| 1 => 1
| m + 2 => k * g k (m + 1) + g k m

/- Let $k$ be an integer. Let $U_k$ be the $2 \times 2$ matrix $\begin{pmatrix} k & 1 \\ 1 & 0 \end{pmatrix}$.
Define a sequence $(g_m)_{m \ge 0}$ by $g_0 = 0$, $g_1 = 1$, and $g_{m+2} = k g_{m+1} + g_m$ for all integers $m \ge 0$.
Show that for any integer $n \ge 0$, the matrix power $(U_k)^{n+1}$ is given by
$$ (U_k)^{n+1} = \begin{pmatrix} g_{n+2} & g_{n+1} \\ g_{n+1} & g_{n} \end{pmatrix} $$ -/
theorem number_theory_637611 {k : ℤ} : ∀ n, (U k) ^ (n + 1) = !![g k (n + 2), g k (n + 1); g k (n + 1), g k n] := by
  intros n
  -- We will use mathematical induction on $n$.
  induction n with
  | zero =>
      -- The base case is true by straightforward verification.
      simp [U, g]
  | succ j ih =>
      -- First, $(U_k)^{j+2} = (U_k)^{j+1} U_k$.
      conv =>
        lhs
        rw [pow_succ]
      rw [ih]
      simp [U]
      ring_nf
      -- Now we use the recurrence relation $g\_{m+2} = k g\_{m+1} + g_m$ to simplify the entries of this matrix.
      -- For the top-left entry, $k g\_{j+2} + g\_{j+1} = g\_{j+3}$
      conv =>
        rhs
        enter [1, 1]
        simp
        rw [add_comm]
        unfold g
      -- For the bottom-left entry, $k g\_{j+1} + g\_{j} = g\_{j+2}$
      conv =>
        rhs
        enter [2, 1, 1]
        rw [add_comm]
        unfold g
      ring_nf
