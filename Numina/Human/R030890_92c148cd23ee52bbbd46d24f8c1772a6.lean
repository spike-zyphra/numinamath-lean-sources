import Mathlib

open Nat
/- When $(a−b)^n$,$n≥2,ab\neq 0$, is expanded by the binomial theorem, it is found that when $a=kb$, where
$k$ is a positive integer, the sum of the second and third terms is zero. Then $n$ equals:
$(A)\frac{1}{2}k(k−1)\ (B) \frac{1}{2}k(k+1)\ (C) 2k−1\ (D) 2k\ (E) 2k+1$ -/
theorem algebra_95886 {a b : ℝ} (n k:Nat) (hab : a*b ≠ 0) (twolen:2≤n) (kpos:0<k) (hk :a = k * b) (h:-(n.choose 1) * a^(n-1)* b + (n.choose 2) * a^(n-2) * b^2 = 0) : n = 2 * k + 1 := by
--Since $a=kb$, we can write $(a-b)^n$ as $(kb-b)^n$
--Expanding, the second term is $-\binom{n}{1}k^{n-1}b^n$, and the third term is $\binom{n}{2}k^{n-2}b^2$
    rw[hk] at h
    ring_nf at h
    rw[mul_assoc,mul_assoc _ (b^2) (b^(n-2)),show b*b^(n-1)=b^1*b^(n-1) by ring,←pow_add,←pow_add,Nat.add_sub_cancel' (by linarith),Nat.add_sub_cancel' (by linarith),mul_assoc,mul_assoc,mul_comm (b^n),←mul_assoc,←mul_assoc,←neg_mul,←add_mul,← neg_mul] at h
--So we get the equation $-\binom{n}{1}k^{n-1}b^n+\binom{n}{2}k^{n-2}b^2=0$.
    have :b^n≠0:=by
      simp only [ne_eq, pow_eq_zero_iff', not_and, Decidable.not_not,(mul_ne_zero_iff.mp hab).2,IsEmpty.forall_iff]
--Dividing by $b^n$, we get $-\binom{n}{1}k^{n-1}+\binom{n}{2}k^{n-2}=0$
    rw[mul_eq_zero_iff_right this] at h
    have :k^(n-2)≠0:=by
      simp only [ne_eq, pow_eq_zero_iff', not_and, Decidable.not_not]
      contrapose! kpos;rw[kpos.1]
--Dividing by $k^{n-2}$, we get $-\binom{n}{1}k+\binom{n}{2}=0$
    rw[mul_comm,show n-1=n-2+1 by norm_num;rw[Nat.sub_add_cancel twolen],pow_add,mul_assoc,←mul_add,] at h
    rw[mul_eq_zero_iff_left (by norm_cast)] at h
    rw[choose_one_right,pow_one,Nat.cast_choose_two,mul_neg,mul_comm,←mul_neg,←mul_div,←mul_add] at h
--Since $n\geq 2$, we can divide by $n$. We get $-k+\frac{n-1}{2}=0$
    rw[mul_eq_zero_iff_left] at h
    field_simp at h
    rw[←@Nat.cast_inj Real,cast_add,cast_mul,cast_one,cast_two]
--So $n=2k+1$.
    linarith
    norm_cast
    linarith