import Mathlib

/- Let $S(N)$ be the number of 1's in the binary representation of an integer $N$, and let $D(N) = S(N + 1) - S(N)$.  Compute the sum of $D(N)$ over all $N$ such that $1 \le N \le 2017$ and $D(N) < 0$. -/
theorem number_theory_46833 (S : ℕ → ℕ) (hS : ∀ n, S n = (Nat.digits 2 n).sum) (D : ℕ → ℤ) (hD : ∀ n, D n = S (n + 1) - S n) :
    ∑ n in (Finset.Icc 1 2017).filter (fun n => D n < 0), D n = -1002 := by 
  simp_all [hD, hS]
  apply Eq.symm
  native_decide