import Mathlib

/- Let $k$ be an integer greater than or equal to 2. Let $d$ be a digit from 1 to 9.
Let $N_j(d)$ denote the integer formed by $j$ repetitions of the digit $d$. For example, if $d=2$ and $j=3$, then $N_j(d) = 222$.
Determine the ones digit of the expression $N_k(d) - N_{k-1}(d) - N_{k-2}(d) - \dots - N_1(d)$.
Show the answer is $( (2-k)d ) \pmod{10}$, where the result is taken in $\{0, 1, \dots, 9\}$. -/
theorem number_theory_635166 {k d:ℕ} (hk: k ≥ 2)
  (hd1: d ≥ 1) (hd2: d ≤ 9) {N: ℕ → ℕ}
  (N_def: ∀j, j ≥ 1 → N j = ∑ i ∈ Finset.range j, d * 10^i):
  N k - (∑ i ∈ Finset.Icc 1 (k-1), N i) ≡ (2-k:ℤ)*d [ZMOD 10] := by

  -- N_j(d) mod 10 = d mod 10, for any j.
  -- it is because N_j(d) = ddd...d (iterate j times), its ones digit is d.
  have h1: ∀j ∈ Finset.Icc 1 (k-1), N j ≡ d [ZMOD 10] := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    rw [N_def j hj.left]
    have: j = j-1 + 1 := by simp [hj.left]
    rw [this, Finset.sum_range_succ']
    simp only [pow_zero, mul_one, Nat.cast_add, Nat.cast_sum,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    nth_rw 3 [← zero_add (d:ℤ)]
    refine Int.ModEq.add ?_ rfl
    change (∑ i ∈ Finset.range (j-1), (d:ℤ)*10^(i+1)) % 10 = 0
    rw [Finset.sum_int_mod]
    have: ∀ i ∈ Finset.range (j-1), (d:ℤ)*10^(i+1) % 10 = 0 := by
      intro i hi
      rw [pow_succ, ← mul_assoc]
      simp only [Int.mul_emod_left]
    rw [Finset.sum_congr rfl this]
    simp

  -- so the sum term mod 10 eq (k-1) d
  have h2: ∑ i ∈ Finset.Icc 1 (k-1), N i ≡
    (k-1) * d [ZMOD 10] := by
    change (∑ i ∈ Finset.Icc 1 (k-1), (N i:ℤ)) % 10 = ((k-1:ℤ) * d) % 10
    change ∀ j ∈ Finset.Icc 1 (k-1), (N j:ℤ) % 10 = d % 10 at h1
    rw [Finset.sum_int_mod, Finset.sum_congr rfl h1, ← Finset.sum_int_mod]
    simp only [Finset.sum_const,
    Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
    congr 2
    omega

  -- and N k mod 10 is d, so add together is (2-k)d
  have: (2-k:ℤ)*d = d - (k-1:ℤ)*d := by ring
  rw [this]
  push_cast
  apply Int.ModEq.sub ?_ h2
  rw [N_def k (by omega)]
  push_cast
  have: k = k-1 + 1 := by omega
  rw [this, Finset.sum_range_succ']
  simp only [pow_zero, mul_one]
  nth_rw 3 [← zero_add (d:ℤ)]
  apply Int.ModEq.add ?_ rfl
  change (∑ i ∈ Finset.range (k-1), (d:ℤ)*10^(i+1)) % 10 = 0
  rw [Finset.sum_int_mod]
  simp only [pow_succ, ← mul_assoc, Int.mul_emod_left,
  Finset.sum_const_zero, EuclideanDomain.zero_mod]