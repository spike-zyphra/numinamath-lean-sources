import Mathlib

/- 4. Given $P_{1}\left(x_{1}, y_{1}\right), P_{2}\left(x_{2}, y_{2}\right), \cdots$, $P_{n}\left(x_{n}, y_{n}\right), \cdots$, where $x_{1}=1, y_{1}=0, x_{n+1}=$ $x_{n}-y_{n}, y_{n+1}=x_{n}+y_{n}\left(n \in \mathbf{Z}_{+}\right)$. If $a_{n}=$ $\overrightarrow{P_{n} P_{n+1}} \cdot \overrightarrow{P_{n+1} P_{n+2}}$, then the smallest positive integer $n$ that satisfies $\sum_{i=1}^{n} a_{i}>1000$ is $n=$ $\qquad$ -/
theorem algebra_148894 {a x y : ℕ → ℝ}
  (hx0 : x 0 = 1) (hy0 : y 0 = 0)
  (hx : ∀ n, x n.succ = x n - y n)
  (hy : ∀ n, y n.succ = x n + y n)
  (ha : ∀ n, a n = (x n.succ - x n) * (x (n + 2) - x n.succ) + (y n.succ - y n) * (y (n + 2) - y n.succ)) :
  IsLeast {n | ∑ i ∈ Finset.range n, a i > 1000} 10 := by
  -- prove a n = 2^n by induction on n
  have a_form : ∀ n, a n = 2^n
  · intro n
    induction n with
  | zero => rw [ha 0, hx 1, hy 1, hx 0, hy 0, hx0, hy0]; norm_num
  | succ n ih =>
    calc
      _ = 2 * ((x n.succ - x n) * (x (n + 2) - x n.succ) + (y n.succ - y n) * (y (n + 2) - y n.succ)) := by
        rw [ha n.succ, hx (n + 2), hy (n + 2), hx n.succ, hy n.succ, hx n, hy n]; ring
      _ = 2^n.succ := by rw [←ha n, ih]; exact (pow_succ' 2 n).symm
  conv => arg 1; arg 1; ext n; lhs; rw [Finset.sum_congr rfl (fun i hi ↦ a_form i), geom_sum_eq one_lt_two.ne.symm n]
  constructor
  -- n = 10 works
  · simp only [gt_iff_lt, Set.mem_setOf_eq]; norm_num
  -- in fact n = 10 is the least, since when n = 9 the sum is 512
  intro n hn
  norm_num at hn
  by_contra hn'
  rw [not_le] at hn'
  absurd calc
    (1000 : ℝ) + 1 < (2^n - 1) + 1 := add_lt_add_right hn 1
    _ = 2^n := by ring
    _ ≤ 2^9 := (pow_le_pow_iff_right₀ one_lt_two).mpr (Nat.le_of_lt_succ hn')
    _ = 512 := by norm_num
  norm_num