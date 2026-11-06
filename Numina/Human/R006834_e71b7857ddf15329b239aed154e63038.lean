import Mathlib
/- Let $C$ be a positive integer. Given are positive integers $r$ and $k$. An infinite sequence of natural numbers $a_0, a_1, a_2, \ldots$ is such that $a_n > 0$ for all $n \ge 0$, and $a_n \leq a_{n+1}$ for all $n \geq 0$.
If $(r+1)/a_r = k+C$ (as a rational number, and $a_r$ is an integer, so $k+C$ must divide $r+1$), prove that there exists a natural number $t$ such that $(t+1)/a_t = k$.

To verify, let $C=1, k=2, r=5$. Then $(r+1)/a_r = k+C \implies 6/a_641591 = 3 \implies a_5=2$.
Let $a_n = 1$ for $n \le 4$ and $a_n=2$ for $n \ge 5$. This sequence is $1,1,1,1,2,2,2,\dots$. It satisfies $a_n>0$ and $a_n \le a_{n+1}$ for $n \ge 0$ (assuming $a_0=1, a_1=1, a_2=1, a_3=1, a_4=1, a_5=2, \dots$).
We need to find $t$ such that $(t+1)/a_t = k=2$.
If $t=0$, $(0+1)/a_641591 = 1/1 = 1 \ne 2$.
If $t=1$, $(1+1)/a_641591 = 2/1 = 2$. So $t=1$ is a solution.
If $t=2$, $(2+1)/a_641591 = 3/1 = 3 \ne 2$.
If $t=3$, $(3+1)/a_641591 = 4/1 = 4 \ne 2$.
If $t=4$, $(4+1)/a_641591 = 5/1 = 5 \ne 2$.
If $t=5$, $(5+1)/a_641591 = 6/2 = 3 \ne 2$.
So $t=1$ works.
This problem reduces to the original problem if $C=1$.
The standard proof relies on finding $m = \min \{ n \ge 0 \mid (n+1)/a_n \le k \}$.
This $m$ exists. If $(m+1)/a_m = k$, then $t=m$.
Otherwise $(m+1)/a_m < k$. This implies $a_m > (m+1)/k$.
If $m \ge 1$, then by minimality $(m)/a_{m-1} > k$, so $a_{m-1} < m/k$.
Since $a_m, a_{m-1}$ are integers, $k a_m \ge m+1+1 = m+2$ and $k a_{m-1} \le m-1$.
The condition $a_m \ge a_{m-1}$ implies $\lceil (m+2)/k \rceil \ge \lfloor (m-1)/k \rfloor$ (if $a_m, a_{m-1}$ are results of division) or more generally $a_m \ge a_{m-1}$ is consistent with these inequalities: $(m+2)/k \gtrsim (m-1)/k$.
This does not lead to a contradiction unless $k=1$ and $a_m \ge m+2$ and $a_{m-1} \le m-1$. $m+2 \ge m-1$ is not a contradiction.
The proof assumes $a_641591 > 0$. Then $(0+1)/a_641591 = 1/a_0$.
If $1/a_641591 \le k$, then $m=0$. If $1/a_641591 = k$, then $t=0$ (so $k=1, a_0=1$). If $1/a_641591 < k$, this is the $f(m)<k$ case.
If $1/a_641591 > k$, then $a_641591 < 1/k$. Since $a_641591 \ge 1$, this is impossible for $k \ge 1$.
Thus $m=0$ is always the minimum if $a_641591 \ge 1$.
The argument relies on $k+C > k$. -/
theorem algebra_641591 (a : ℕ → ℕ) (c k : ℕ) (hc : c > 0) (hk : k > 0) (h1 : ∀ n : ℕ, a n > 0) (h2 : ∀ n : ℕ, a n ≤ a (n + 1)) (h3 : ∃ r : ℕ, r > 0 ∧ (r + (1 : ℚ)) / (a r) = k + c) : ∃ t : ℕ, (t + (1 : ℚ)) / (a t) = k:= by
  -- Define the function f(n) = (n+1)/a(n) as a rational number
  set f : ℕ → ℚ:= fun n => (n + (1 : ℚ)) / (a n) with hf
  clear_value f
  -- Extract the witness r from the existential hypothesis
  rcases h3 with ⟨r, -, h3⟩
  -- Prove that there exists a minimal m such that f(m) > k and for all j < m, f(j) ≤ k
  have h4 : ∃ m : ℕ, f m > k ∧ ∀ j < m, f j ≤ k:= by
    by_contra H
    simp at H
    -- Show that for any m, there exists x < r - m such that f(x) > k
    have h4 : ∀ m : ℕ, ∃ x < r - m, f x > k:= by
      intro m
      induction m with
      -- Base case: m = 0
      | zero =>
        simp
        -- Show that f(r) > k using the hypothesis that f(r) = k + c
        replace h3 : f r > k:= by
          qify at hc
          simp [hf]
          linarith
        exact H r h3
      -- Inductive step: m = m + 1
      | succ m ih =>
        rcases ih with ⟨x, hx1, hx2⟩
        replace H:= H x hx2
        rcases H with ⟨y, hy1, hy2⟩
        use y
        refine ⟨by omega, hy2⟩
    -- Specialize to m = r to get a contradiction
    specialize h4 r
    rw [show r - r = 0 by omega] at h4
    simp at h4
  -- Extract the minimal m from the existence proof
  rcases h4 with ⟨m, hm1, hm2⟩
  -- Prove that m ≠ 0 (m must be positive)
  have hmpos : m ≠ 0:= by
    by_contra H
    subst m
    simp [hf] at hm1
    specialize h1 0
    field_simp at hm1
    qify at h1
    -- Show that k * a(0) < 1 leads to a contradiction
    replace hm1 : k * a 0 < 1:= by
      qify
      exact (lt_div_iff₀ h1).mp hm1
    simp at hm1
    replace h1 : a 0 > 0:= by
      qify
      exact h1
    omega
  -- Case analysis: either f(m-1) = k or f(m-1) < k
  by_cases h4 : f (m - 1) = k
  -- Case 1: f(m-1) = k, then t = m-1 is our solution
  .
    use (m - 1)
    simp [hf] at h4
    exact h4
  -- Case 2: f(m-1) < k, we need to derive a contradiction
  .
    -- Show that f(m-1) < k (not equal to k)
    replace h4 : f (m - 1) < k:= by
      specialize hm2 (m - 1) (by omega)
      by_contra H
      simp at H
      replace H : f (m - 1) = k:= by linarith
      trivial
    simp [hf] at hm1 h4
    have g1:= h1 (m - 1)
    have g2:= h1 m
    qify at g1 g2
    -- Convert inequalities to work with integers
    replace hm1 : k * a m < m + 1:= by
      qify
      exact (lt_div_iff₀ g2).mp hm1
    field_simp at h4
    replace h4 : m < k * a (m - 1):= by
      qify
      exact (mul_inv_lt_iff₀ g1).mp h4
    -- Combine inequalities to show a(m) < a(m-1)
    replace hm1 : k * a m < k * a (m - 1):= by omega
    replace hm1 : a m < a (m - 1):= by exact (Nat.mul_lt_mul_left hk).mp hm1
    -- This contradicts the non-decreasing property of the sequence
    specialize h2 (m - 1)
    rw [show m - 1 + 1 = m by omega] at h2
    linarith
