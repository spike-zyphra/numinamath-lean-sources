import Mathlib

theorem algebra_184110 (n : ℕ) :
    ∑ i in Finset.Icc 1 n, i = n * (n + 1) / 2 ∧
    ∑ i in Finset.Icc 1 n, i * (i + 1) = n * (n + 1) * (n + 2) / 3 ∧
    ∑ i in Finset.Icc 1 n, i^2 = n * (n + 1) * (2 * n + 1) / 6 ∧
    ∑ i in Finset.Icc 1 n, i^3 = n^2 * (n + 1)^2 / 4 := by 
  constructor
  · -- First identity: Prove that $1+2+\cdots+n=\frac{1}{2}n(n+1)$
    induction n with
    | zero =>
      simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by norm_num), ih]
      ring_nf
      <;> omega
  constructor
  · -- Second identity: Prove that $1\cdot2+2\cdot3+\cdots+n(n+1)=\frac{1}{3}n(n+1)(n+2)$
    induction n with
    | zero =>
      simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by norm_num), ih]
      ring_nf
      <;> omega
  constructor
  · -- Third identity: Prove that $1^2+2^2+\cdots+n^2=\frac{1}{6}n(n+1)(2n+1)$
    induction n with
    | zero =>
      simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by norm_num), ih]
      ring_nf
      <;> omega
  · -- Fourth identity: Prove that $1^3+2^3+\cdots+n^3=\frac{1}{4}n^2(n+1)^2$
    induction n with
    | zero =>
      simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by norm_num), ih]
      ring_nf
      <;> omega