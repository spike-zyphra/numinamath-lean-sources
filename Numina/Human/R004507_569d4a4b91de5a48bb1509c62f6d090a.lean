import Mathlib

/- Define a computable sequence $a_n$, which is equal to $x_n$ in the problem statement. -/
def a : ℕ → ℕ
| 0 => 0
| 1 => 1
| n + 1 => (a n) + (a n).sqrt

/- $a_{n+1} = a_n + \lfloor \sqrt{a_n} \rfloor$ forall $n \geq 1$ by definition. -/
lemma a_def {n : ℕ} (hn : 1 ≤ n) : a (n + 1) = a n + (a n).sqrt := by
  cases n with
  | zero => simp at hn
  | succ n => simp [a]

/- We show that $x_n = a_n$ forall $n \geq 1$. -/
lemma lemma_1 {x : ℕ → ℝ} (hx1 : x 1 = 1) (hxn : ∀ n > 0, x (n + 1) = x n + ⌊√(x n)⌋) (n : ℕ) (hn : 1 ≤ n) : x n = a n := by
  -- Use induction with base case $n = 1$ and inductive step $n \to n + 1$.
  -- The lemma `Real.floor_real_sqrt_eq_nat_sqrt`, which is a `@[simp]` lemma, helps us identify `⌊√x⌋` and `x.sqrt`.
  induction n, hn using Nat.le_induction with
  | base => simp [hx1, a]
  | succ n hn ih => simp [a_def hn, hxn n hn, ih]

/- 8. In the sequence $\left\{a_{n}\right\}_{n=1}^{+\infty}$, $x_{1}=1$, if for any positive integer $n$ there is $x_{n+1}=x_{n}+\left[\sqrt{x_{n}}\right]$, where the symbol $[x]$ denotes the greatest integer not exceeding $x$, then the smallest positive integer $n$ such that $x_{n} \geqslant 2019$ is $\qquad$. -/
theorem number_theory_276742 (x : ℕ → ℝ) (hx1 : x 1 = 1)
    (hxn : ∀ n > 0, x (n + 1) = x n + ⌊√(x n)⌋) :
    IsLeast {n | 0 < n ∧ x n ≥ 2019} 95 := by
  constructor
  . -- We show $x_95 \geq 2019$ by computing $x_95 = a_95$ explicitly.
    simp [lemma_1 hx1 hxn]
    native_decide
  . intro n ⟨hn, h⟩
    -- We show that $x_n < 2019$ forall $0 < n < 95$.
    contrapose! h with hn'
    -- We rewrite it as $∀ n < 95, 0 < n → a_n < 2019$.
    -- So it can be solved by direct computation.
    simp [lemma_1 hx1 hxn n hn]
    revert hn
    revert n
    native_decide
