import Mathlib

/- Let $n$ be a natural number such that $1 \le n \le 99$. We define a sequence by starting with $n_0 = n$, and for $k \ge 0$, $n_{k+1} = n_k - S(n_k)$, where $S(x)$ is the sum of the decimal digits of $x$. Prove that $n_{15} = 0$. -/
theorem number_theory_635301 (n : ℕ) (hn : n ∈ Finset.Icc 1 99) (ns : ℕ → ℕ) (hns₀ : ns 0 = n) (hns : ∀ k, ns (k + 1) = ns k - (Nat.digits 10 (ns k)).sum) :
    ns 15 = 0 := by
  -- We show that the sequence n_k = f^[k] n, where f(n) = n - (Nat.digits 10 n).sum, and f^[k] is the k-th iterate of f.
  have H (k : ℕ) : ns k = (fun n => n - (Nat.digits 10 n).sum)^[k] n := by
    -- Easily shown by induction.
    induction k with
    | zero => simp [hns₀]
    | succ k ih => simp only [Function.iterate_succ', Function.comp_apply, ←ih, hns]
  rw [H]
  clear ns hns₀ hns H
  -- We quantify over all possible values of n and check that n_{15} = 0.
  revert n
  native_decide