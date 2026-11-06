import Mathlib

/- Consider the sequence defined recursively by $u_1 = a > 0$ and
\[u_{n + 1} = -\frac{1}{u_n + 1}\]for $n \ge 1.$  Express $u_{16}$ in terms of $a.$ -/
theorem algebra_13907 {a : ℝ} (ha : a > 0) (u : ℕ → ℝ)
    (hu1 : u 1 = a) (hun : ∀ n ≥ 1, u (n + 1) = -1 / (u n + 1)) :
    u 16 = a := by
  induction 15 <;> simp_all [hu1, hun, Nat.lt_succ_iff]
  <;> field_simp <;> linarith