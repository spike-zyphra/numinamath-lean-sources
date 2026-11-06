import Mathlib

/- Given an odd function $f(x)$ defined on $\mathbb{R}$ that satisfies $f\left( \frac {3}{2}-x\right)=f(x)$ and $f(-2)=-3$, and let $S_{n}$ be the sum of the first $n$ terms of the sequence $\{a_{n}\}$, with $S_{n}=2a_{n}+n$. Find the value of $f(a_{5})+f(a_{6}) = 3$. -/
theorem algebra_9285 {f : ℝ → ℝ} (hf : ∀ (x : ℝ), f (-x) = -f x) (h : ∀ x, f (3 / 2 - x) = f x)
  (h' : f (-2) = -3) (a : ℕ → ℝ) (ha : ∀ n, ∑ i ∈ Finset.range n, a (i + 1) = 2 * a n + n) :
  f (a 5) + f (a 6) = 3 := by
  -- proof of f(x) = f(x + 3)
  have fperiod : ∀x, f x = f (x + 3) := by
    intro x
    have odd := hf (-x)
    -- f(3+x)=f\left[ \frac {3}{2}-(- \frac {3}{2}-x)\right]=-f\left[ \frac {3}{2}-(-x)\right]=-f(-x)=f(x)$.
    rw [show x + 3 = 3/2 - (-3/2 - x) by ring_nf]
    rw [h (-3/2 - x)]
    rw [show -3 / 2 - x = -(3/2 + x) by ring_nf]
    rw [hf (3/2 + x)]
    have hx : f (3 / 2 + x) = f (-x) := by
      have hxx := h (-x)
      simp at hxx
      exact hxx
    rw [hx]
    rw [show -f (-x) = f x by
      rw [hf (x)]
      simp
    ]
  -- proof of $a_{n} = 1 - 2^n$
  have haeq : a = fun (n : ℕ) => 1 - 2^n := by
    ext x
    induction x with
    -- proof of $a_0 = 0$
    | zero =>
      have t := ha 0
      simp at t
      simp
      exact t
    | succ n hn =>
      -- $S_{n+1}=2a_{n+1}+n+1$,
      have t := ha (n+1); simp at t
      -- $S_{n}=2a_{n}+n$,
      have tt := ha n; simp at tt
      -- split $S_{n+1} = S_{n} + a_{n+1}$
      rw [Finset.sum_range_add] at t; simp at t
      -- using $a_{n} = 1 - 2 ^ n$ and $S_{n}=2a_{n}+n$, we get $2 * (1 - 2 ^ n) + ↑n + a (n + 1) = 2 * a (n + 1) + (↑n + 1)$
      rw [tt, hn] at t
      -- simplify, we get $a_{n} = 1 - 2^n$
      replace t := congrArg (fun v => v - (a (n+1))) t; simp at t
      rw [two_mul] at t;
      ring_nf at t
      replace t := congrArg (fun (v : ℝ)=> v - (1+n)) t; simp at t
      ring_nf at t
      rw [← pow_succ] at t
      symm
      rw [show 1 + n = n + 1 by ring_nf] at t
      exact t
  rw [haeq]
  simp
  ring_nf
  -- proof $f(3*n + x) = f(x)$ based on $f(x+3) = f(x)$
  have fperiod2 : ∀(x : ℝ)(n : ℕ), f (3 * n + x) = f x := by
    intro x n
    induction n with
    | zero =>
      simp
    | succ n hn =>
      rw [show 3 * ↑(n + 1) + x = 3 * ((n : ℝ)+ (1 : ℝ)) + x by simp]
      rw [mul_add]; simp;
      rw [show 3 * ↑n + 3 + x = (3 * ↑n + x) + 3 by ring_nf]
      rw [← (fperiod (3 * ↑n + x))]
      exact hn
  -- $f(a_{5})+f(a_{6})=f(-31)+f(-63)=f(2)+f(0)=f(2)=-f(-2)=3$.
  rw [hf 31, hf 63]
  rw [show -f 31 + -f 63 = -f (3 * (11 : ℕ) + (-2 : ℝ)) + -f (3 * (21 : ℕ) + 0) by ring_nf]
  rw [fperiod2 (-2) 11]
  rw [fperiod2 0 21]
  rw [h']
  have f0eq0 : f 0 = 0 := by
    have hf' := hf 0
    simp at hf'
    linarith
  rw [f0eq0]
  simp
