import Mathlib
open Polynomial

/- Given the sequence $a_{0}, a_{1}, a_{2}, \cdots$ satisfies $a_{0} \neq a_{1}$ and

$$
a_{i-1}+a_{i+1}=2 a_{i} \quad (i=1,2,3, \cdots),
$$

Prove: For any natural number $n$,

$$
\begin{aligned}
p(x)= & a_{0} C_{n}^{0}(1-x)^{n}+a_{1} C_{n}^{1} x (1-x)^{n-1}+a_{2} C_{n}^{2} x^2 (1-x)^{n-2} \\
& +\cdots+a_{n-1} C_{n}^{n-1} x^{n-1} (1-x)+a_{n} C_{n}^{n} x^{n}
\end{aligned}
$$

is a linear polynomial in $x$. -/
theorem algebra_102333 {a : ℕ → ℝ} (ha : a 0 ≠ a 1)
    (h : ∀ i, a i + a (i + 2) = 2 * a (i + 1)) :
    ∀ n > 0, ∃ p : Polynomial ℝ, p.degree = 1 ∧
      ∀ x, p.eval x = ∑ i ∈ Finset.range (n + 1),
        a i * Nat.choose n i * x^i * (1 - x) ^ (n - i) := by
  -- show a is an arithmetic progression with an easy induction
  have a_arith : ∀ i, a i = a 0 + i * (a 1 - a 0)
  · intro i
    induction' i using Nat.strongRec with i ih
    match i with
    | 0 => simp only [Nat.cast_zero, zero_mul, add_zero]
    | 1 => simp only [Nat.cast_one, one_mul, add_sub_cancel]
    | j + 2 =>
    rw [show a (j + 2) = 2 * a (j + 1) - a j by linarith [h j],
        ih (j + 1) (by linarith), ih j (by linarith),
        Nat.cast_add, Nat.cast_add]
    ring
  intro n hn
  -- define the linear polynomial
  let p : Polynomial ℝ := C (a 0) + C (n * (a 1 - a 0)) * X
  use p
  constructor
  -- show p.degree = 1
  · unfold p
    compute_degree
    apply mul_ne_zero
    exact_mod_cast hn.ne.symm
    exact sub_ne_zero_of_ne ha.symm
    exact Nat.one_le_iff_ne_zero.mpr fun eq => ha (congrArg a eq.symm)

  intro x
  -- when x = 0 or x = 1 then both expressions are zero
  by_cases hx : x = 0
  · simp [p, hx, zero_pow_eq]
  by_cases hx1 : x = 1
  · simp [p, hx1, zero_pow_eq]
    rw [Finset.sum_range_succ, Finset.sum_eq_zero, ←a_arith n]
    simp
    intro i hi
    rw [Finset.mem_range] at hi
    simp [Nat.sub_ne_zero_iff_lt.mpr hi]
  
  -- substitute x into p
  simp only [p, map_sub, eval_add, eval_C, eval_mul, eval_sub, eval_X]

  -- use the binomial formula on the second term and cancel it
  conv_rhs =>
    arg 2
    intro i
    rw [a_arith i, add_mul, add_mul, add_mul, mul_assoc, mul_comm (_ * _) _, mul_comm (a 0) _, ← mul_assoc]
  rw [Finset.sum_add_distrib, ←Finset.sum_mul, ←add_pow x (1 - x)]
  simp only [add_sub_cancel, one_pow, one_mul, add_right_inj]

  -- for the first term, we reindex the sum
  have summand_pos : ∀ i, ↑i * (a 1 - a 0) * ↑(n.choose i) * x ^ i * (1 - x) ^ (n - i) ≠ 0 → i > 0
  · intro i hi
    apply Nat.zero_lt_of_ne_zero
    rw [show ↑i * (a 1 - a 0) * ↑(n.choose i) * x ^ i * (1 - x) ^ (n - i) = ↑i * ((a 1 - a 0) * ↑(n.choose i) * x ^ i * (1 - x) ^ (n - i)) by ring] at hi
    exact_mod_cast left_ne_zero_of_mul hi
  have sum_rw : ∑ i ∈ Finset.range (n + 1), i * (a 1 - a 0) * ↑(n.choose i) * x^i * (1 - x) ^ (n - i)
    = ∑ i ∈ Finset.range (n-1+1), x^i.succ * (1 - x)^(n - i.succ) * ↑((n - 1).succ.choose i.succ * i.succ) * (a 1 - a 0)
  · apply Finset.sum_bij_ne_zero (fun a ha haf => a - 1)
    · intro i hi hf
      simp at hi ⊢
      rw [Nat.sub_one_add_one_eq_of_pos hn]
      apply Nat.sub_lt_right_of_lt_add (summand_pos i hf) hi
    · intro i hi hf j hj hg hneg
      exact Nat.sub_one_cancel (summand_pos i hf) (summand_pos j hg) hneg
    · intro j hj hg
      use j + 1
      simp at hj
      rw [Nat.sub_one_add_one_eq_of_pos hn] at hj
      have hb : j + 1 ∈ Finset.range (n + 1) := by simp; exact hj
      use hb
      have hg : ↑(j + 1) * (a 1 - a 0) * ↑(n.choose (j + 1)) * x ^ (j + 1) * (1 - x) ^ (n - (j + 1)) ≠ 0
      · apply mul_ne_zero
        apply mul_ne_zero
        apply mul_ne_zero
        apply mul_ne_zero _ (sub_ne_zero_of_ne ha.symm)
        exact_mod_cast (NeZero.ne' (j + 1)).symm
        exact_mod_cast (Nat.choose_pos hj).ne.symm
        exact pow_ne_zero (j + 1) hx
        exact pow_ne_zero _ (sub_ne_zero_of_ne fun a => hx1 a.symm)
      use hg
      rfl
    · intro i hi hf
      rw [
        show (i-1).succ = i-1+1 by rfl,
        show (n-1).succ = n-1+1 by rfl,
        Nat.sub_one_add_one_eq_of_pos (summand_pos i hf),
        Nat.sub_one_add_one_eq_of_pos hn,
        Nat.cast_mul
      ]
      ring
  rw [sum_rw]
  -- use a binomial identity on the summand
  have summand_rw : ∀ i ∈ Finset.range (n - 1 + 1),
    x^i.succ * (1 - x)^(n - i.succ) * ↑((n - 1).succ.choose i.succ * i.succ) * (a 1 - a 0)
    = x^i * (1 - x)^(n - 1 - i) * ↑((n - 1).choose i) * (x * ↑n * (a 1 - a 0))
  · intro i hi
    simp at hi
    rw [Nat.sub_one_add_one_eq_of_pos hn] at hi
    have n_sub : n-i.succ = n-1-i
    · apply (Nat.sub_eq_iff_eq_add' hi).mpr
      rw [Nat.sub_sub n 1 i,
          ←Nat.add_sub_assoc (Nat.one_add_le_iff.mpr hi),
          add_comm, ←Nat.sub_sub, Nat.sub_eq_of_eq_add]
      rfl
    rw [n_sub, ←Nat.succ_mul_choose_eq,
      show (n-1).succ = n-1+1 by rfl,
      Nat.sub_one_add_one_eq_of_pos hn,
      pow_succ, Nat.cast_mul]
    ring
  -- conclude using the binomial theorem again
  rw [Finset.sum_congr rfl summand_rw, ←Finset.sum_mul, ←add_pow x (1 - x)]
  ring