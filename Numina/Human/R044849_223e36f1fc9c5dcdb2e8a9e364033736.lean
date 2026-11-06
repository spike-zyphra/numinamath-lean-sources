import Mathlib

/- Originally given matrix `U=[1,1; 0,1]` which is wrong.
It should be `U=[1,1; 1,0]`. -/
abbrev U : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, 0]

/- Fibonacci number -/
abbrev fib : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/- **The original problem is wrong. Following is the correct version.**
Let $ U = \begin{pmatrix} 1 & 1 \\ 1 & 0 \end{pmatrix} $.
a) Show that $ U^{n} = \begin{pmatrix} u_{n+1} & u_{n} \\ u_{n} & u_{n-1} \end{pmatrix} $, where $ u_n $ represents the $ n $-th Fibonacci number.
-/
theorem number_theory_4548_1 {n : ℕ} (h_posn : n ≥ 0) :
    U ^ (n + 1) = !![fib (n + 2), fib (n + 1); fib (n + 1), fib (n)] := by
  -- use mathematical induction
  induction n with
  -- check base case
  | zero => norm_num
  | succ n ih =>
    -- use the fact that `U^(n+1)=U^n*U`
    -- we can draw a conclusion from induction hypothesis after simple calculation
    rw [pow_succ, ih (Nat.zero_le n), U]
    norm_num
    ring_nf

/- **The original problem is wrong. Following is the correct version.**
Let $ U = \begin{pmatrix} 1 & 1 \\ 1 & 0 \end{pmatrix} $.
b) Prove the determinant of $ U^{n}$ is $(-1)^n$ using $fib (n + 1) * fib (n - 1) - (fib n) ^ 2 = (-1) ^ n$.
-/
theorem number_theory_4548_2
    (n : ℕ) (h_posn : n > 0)
    (h : ∀ n, fib (n + 1) * fib (n - 1) - (fib n) ^ 2 = (-1) ^ n) :
    (U ^ n).det = (-1) ^ n := by
  -- apply number_theory_4548_1
  let hh := number_theory_4548_1 ((Nat.le_sub_one_iff_lt h_posn).mpr h_posn)
  rw [Nat.sub_add_cancel h_posn] at hh
  rw [show n - 1 + 2 = n + 1 by exact Eq.symm ((fun {m k n} => Nat.add_right_cancel_iff.mpr) ((Nat.sub_eq_iff_eq_add h_posn).mp rfl))] at hh
  -- apply h
  rw [hh, Matrix.det_fin_two_of, ← pow_two]
  exact h n
