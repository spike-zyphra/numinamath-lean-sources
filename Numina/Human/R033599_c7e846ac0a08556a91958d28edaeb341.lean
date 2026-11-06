import Mathlib
open Polynomial

/- Example 2 Given that $\left\{a_{n}\right\}$ is an arithmetic sequence with a non-zero common difference. Prove: $P_{n}(x)=\sum_{k=0}^{n} a_{k} C_{n}^{k}(1-$ $x)^{n-k} \cdot x^{k}$ is a linear polynomial in $x$.

---

The translation maintains the original text's line breaks and formatting. -/
theorem algebra_172024 {a : ℕ → ℝ} (ha : ∃ d > 0, ∀ n, a n = a 0 + d * n) :
  ∀ n > 0, ∃ p : Polynomial ℝ, p.degree = 1 ∧
    ∀ x, p.eval x = ∑ k ∈ Finset.range (n + 1), a k * Nat.choose n k * (1 - x) ^ (n - k) * x^k := by
  rcases ha with ⟨d, dpos, hd⟩
  intro n hn
  -- define the linear polynomial
  let p : Polynomial ℝ := C (a 0) + C (n * d) * X
  use p
  constructor
  -- show p.degree = 1
  · unfold p
    compute_degree
    apply mul_ne_zero
    exact_mod_cast hn.ne.symm
    exact dpos.ne.symm
    exact Nat.le_of_ble_eq_true rfl
  intro x
  -- when x = 0 or x = 1 then both expressions are zero
  by_cases hx : x = 0
  · simp [p, hx, zero_pow_eq]
  by_cases hx1 : x = 1
  · simp [p, hx1, zero_pow_eq]
    rw [Finset.sum_range_succ, Finset.sum_eq_zero, mul_comm, ←hd n]
    simp
    intro i hi
    rw [Finset.mem_range] at hi
    simp [Nat.sub_ne_zero_iff_lt.mpr hi]

  -- substitute x into p
  simp only [p, map_sub, eval_add, eval_C, eval_mul, eval_sub, eval_X]

  -- rearrange in the summand
  conv_rhs =>
    arg 2
    intro i
    rw [hd i, add_mul, add_mul, add_mul,
      show a 0 * ↑(n.choose i) * (1 - x)^(n - i) * x ^ i = x^i * (1 - x)^(n - i) * (n.choose i) * a 0 by ring,
      show d * i * ↑(n.choose i) * (1 - x)^(n - i) * x^i = x^i * (1 - x)^(n - i) * ((n.choose i) * i) * d by ring,
    ]
  -- use the binomial formula on the second term and cancel it from both sides
  rw [Finset.sum_add_distrib, ←Finset.sum_mul, ←add_pow x (1 - x)]
  simp only [add_sub_cancel, one_pow, one_mul, add_right_inj]

  -- for the first term, we reindex the sum
  have summand_pos : ∀ i, x^i * (1 - x)^(n - i) * ((n.choose i) * i) * d ≠ 0 → i > 0
  · intro i hi
    apply Nat.zero_lt_of_ne_zero
    rw [show x^i * (1 - x)^(n - i) * ((n.choose i) * i) * d = x^i * (1 - x)^(n - i) * (n.choose i) * d * i by ring] at hi
    exact_mod_cast right_ne_zero_of_mul hi
  
  have sum_rw : ∑ i ∈ Finset.range (n + 1), x^i * (1 - x)^(n - i) * (↑(n.choose i) * i) * d
    = ∑ i ∈ Finset.range (n-1+1), x^i.succ * (1 - x)^(n - i.succ) * ↑((n - 1).succ.choose i.succ * i.succ) * d
  · apply Finset.sum_bij_ne_zero (fun a ha haf => a - 1)
    · intro i hi hf
      simp at hi ⊢
      rw [Nat.sub_one_add_one_eq_of_pos hn]
      exact Nat.sub_lt_right_of_lt_add (summand_pos i hf) hi
    · intro i hi hf j hj hg hneg
      exact Nat.sub_one_cancel (summand_pos i hf) (summand_pos j hg) hneg
    · intro j hj hg
      use j + 1
      simp at hj
      rw [Nat.sub_one_add_one_eq_of_pos hn] at hj
      have hb : j + 1 ∈ Finset.range (n + 1) := by simp; exact hj
      use hb
      have hg : x^(j + 1) * (1 - x)^(n - (j + 1)) * (↑(n.choose (j + 1)) * ↑(j + 1)) * d ≠ 0
      · apply mul_ne_zero
        apply mul_ne_zero
        apply mul_ne_zero
        exact pow_ne_zero (j + 1) hx
        exact pow_ne_zero _ (sub_ne_zero_of_ne fun a => hx1 a.symm)
        apply mul_ne_zero
        exact_mod_cast (Nat.choose_pos hj).ne.symm
        exact_mod_cast (NeZero.ne' (j + 1)).symm
        simp only [hd 1, Nat.cast_one, mul_one, add_sub_cancel_left, ne_eq]
        exact dpos.ne.symm
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
  rw [sum_rw]

  -- use a binomial identity on the summand
  have summand_rw : ∀ i ∈ Finset.range (n - 1 + 1),
    x^i.succ * (1 - x)^(n - i.succ) * ↑((n - 1).succ.choose i.succ * i.succ) * d
    = x^i * (1 - x)^(n - 1 - i) * ↑((n - 1).choose i) * (x * ↑n * d)
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