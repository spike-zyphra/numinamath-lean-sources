import Mathlib

/- Example 4 Let the $n$-degree polynomial $f(x)$ satisfy $f(k)=\frac{1}{C_{n+1}^{k}}, k=0,1,2, \cdots, n$, find $f(n+1)$.

 -/
theorem algebra_249317 {n : ℕ} (f : Polynomial ℝ) (hf : f.degree = n)
    (h : ∀ k ∈ Finset.range (n + 1), f.eval (k : ℝ) = 1 / Nat.choose (n + 1) k) :
    f.eval (n + 1 : ℝ) = if Odd n then 0 else 1 := by


  set s := Finset.range (n+1) with s_def
  set v: ℕ → ℝ := fun i => i with v_def
  set r: ℕ → ℝ := fun k => 1 / Nat.choose (n+1) k with r_def
  have hvs: Set.InjOn v s := by
    simp only [v_def, s_def]
    refine Function.Injective.injOn ?_
    exact CharZero.cast_injective

  -- by Lagrange interpolation, we claim f is the unique polynomial defined by those n points.
  have h1: f = Lagrange.interpolate s v r := by
    rw [← Lagrange.eq_interpolate_iff r hvs]
    constructor
    · simp only [hf, s_def, Finset.card_range,
      Nat.cast_add, Nat.cast_one]
      norm_cast
      simp only [lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt]
    · intro i hi
      simp only [v_def, h i hi, r_def]

  -- expand f, we will find it a combinatorial number multiply prod of (x-i)/(k-i) form.
  -- following "have" statements all deal with simplification with combinatorial number and prod (x-i)/(k-i) form.

  -- prod of (m-i) with i ≠ k, simplifies to （m+1）! / k
  have h2 {m k:ℕ} (hk: k ≤ m): (m+1-k) * ∏ i ∈ (Finset.range (m+1)).erase k, (m+1-i:ℝ) =
    (Nat.factorial (m+1)) := by
    replace hk: k ∈ Finset.range (m+1) := Finset.mem_range_succ_iff.mpr hk
    have := Finset.mul_prod_erase (Finset.range (m+1)) (fun (i:ℕ) => (m+1-i:ℝ)) hk
    simp only at this
    rw [this, ← Finset.prod_range_add_one_eq_factorial]
    push_cast
    nth_rw 2 [← Finset.prod_range_reflect]
    apply Finset.prod_congr rfl (fun i hi => ?_)
    replace hi: i ≤ m := Finset.mem_range_succ_iff.mp hi
    rw [add_tsub_cancel_right, Nat.cast_sub hi]
    ring

  -- separate prod of 1/(i-k) into two parts.
  -- treat range (m+1) erase i as range i union i+1 to m.
  -- say, it is k × (k-1) ... × 1,  multiply -1 × -2 ×...× -(n-k).
  -- first part, it is k × (k-1) × ... × 1.
  have h31 {m k:ℕ} (hk: k ≤ m): ∏ i ∈ Finset.range k, (k-i:ℝ) =
    (Nat.factorial k) := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    nth_rw 2 [← Finset.prod_range_reflect]
    push_cast
    apply Finset.prod_congr rfl (fun i hi => ?_)
    simp only [Finset.mem_range] at hi
    rw [Nat.sub_sub, Nat.cast_sub (Nat.one_add_le_iff.mpr hi)]
    push_cast; ring

  -- second part. -1 × -2 × ... × -(n-k)
  have h32 {m k:ℕ} (hk: k ≤ m): ∏ j ∈ (Finset.Ico (k+1) (m+1)), (k-j:ℝ) =
    (-1)^(m-k) * (Nat.factorial (m-k)) := by
    by_cases keqm: k = m
    · simp [keqm]
    have kltm: k < m := lt_of_le_of_ne hk keqm
    rw [← Finset.prod_range_add_one_eq_factorial,
    Finset.prod_range_eq_mul_Ico _ (by omega)]
    simp only [zero_add, one_mul, Nat.cast_prod,
    Nat.cast_add, Nat.cast_one]
    have: m+1 = (m+1-k) + k := by omega
    nth_rw 1 [add_comm k 1, this, ← Finset.prod_Ico_add]
    simp only [Nat.cast_add, sub_add_cancel_left]
    have hh1: m-k = (Finset.Ico 1 (m+1-k)).card := by
      simp only [Nat.card_Ico]
      omega
    have hh2: ∏ i ∈ Finset.Ico 1 (m+1-k), (-i:ℝ) =
      (-1)^(m-k) * ∏ i ∈ Finset.Ico 1 (m+1-k), (i:ℝ) := by
      rw [hh1, Finset.pow_card_mul_prod]
      simp only [neg_mul, one_mul]
    simp only [hh2, mul_eq_mul_left_iff, pow_eq_zero_iff', neg_eq_zero,
    one_ne_zero, ne_eq, false_and, or_false]
    have hh3: 1 < m+1-k := by omega
    rw [Finset.prod_eq_prod_Ico_succ_bot hh3, Nat.cast_one, one_mul]
    have hh4: m+1-k = (m-k) +1 := by omega
    rw [hh4, ← Finset.prod_Ico_add]
    apply Finset.prod_congr rfl ?_
    simp [add_comm]

  -- combine result from h31 and h32
  have h3 {i m:ℕ} (hi: i ≤ m):
    ∏ j ∈ (Finset.range (m+1)).erase i, (i-j:ℝ)⁻¹ =
    (-1)^(m-i) * ((i.factorial: ℝ)⁻¹ * ((m-i).factorial:ℝ)⁻¹) := by
    have hh1: (Finset.range (m+1)).erase i =
      (Finset.range i) ∪ (Finset.Ico (i+1) (m+1)) := by
      clear * - hi
      ext j
      simp only [Finset.mem_erase, ne_eq, Finset.mem_range,
      Finset.mem_union, Finset.mem_Ico]
      by_cases hj: j < i
      · simp only [hj.ne, not_false_eq_true,
        true_and, hj, true_or, iff_true]
        apply lt_trans hj (Order.lt_add_one_iff.mpr hi)
      · simp only [hj, false_or, and_congr_left_iff]
        intro _
        push_neg at hj
        constructor
        · intro hij
          have: i < j := by
            apply lt_of_le_of_ne hj
            exact fun a => hij (id (Eq.symm a))
          exact this
        · intro hij
          replace hij: i < j := by exact hij
          push_neg; exact hij.ne'
    have hh2: Disjoint (Finset.range i) (Finset.Ico (i+1) (m+1)) := by
      rw [Finset.range_eq_Ico]
      have: Disjoint (Finset.Ico 0 (i+1)) (Finset.Ico (i+1) (m+1)) := by
        exact Finset.Ico_disjoint_Ico_consecutive 0 (i+1) (m+1)
      apply Finset.disjoint_of_subset_left ?_ this
      simp
    rw [Finset.prod_inv_distrib, hh1, Finset.prod_union hh2]
    rw [h31 hi, h32 hi]
    ring_nf


  -- combine result from h2 and h3, simplify.
  have h4 {i m:ℕ} (hi: i ≤ m): (-1)^(m-i) * (m+1).choose i =
    ∏ j ∈ (Finset.range (m+1)).erase i, ((i-j:ℝ)⁻¹ * (m+1-j)) := by
    rw [Finset.prod_mul_distrib, h3 hi,
    Nat.choose_eq_factorial_div_factorial (Nat.le_add_right_of_le hi)]
    have hh1: i.factorial * (m+1-i).factorial ∣ (m+1).factorial := by
      use (m+1).choose i
      have: m+1 = (m+1-i) + i := by omega
      nth_rw 1 [this]
      rw [← Nat.add_choose_mul_factorial_mul_factorial, ← this]
      ring
    have hh2: i.factorial * (m+1-i).factorial ≠ 0 := by
      symm; apply ne_of_lt
      apply mul_pos
      <;> apply Nat.factorial_pos
    rw [Nat.cast_div hh1 (by norm_cast), ← h2 hi]
    push_cast; rify at hh2
    field_simp only [hh2]
    have hh3: (m+1-i).factorial = (m+1-i) * (m-i).factorial := by
      have: m+1-i = (m-i) + 1 := by omega
      rw [this, Nat.factorial_succ]
    rw [hh3]; push_cast
    rw [Nat.cast_sub (Nat.le_add_right_of_le hi)]
    push_cast; ring


  -- use above result, we claim f (n+1) is just sum (-1)^(n-i)
  have h5: f.eval (n+1:ℝ) = ∑ i ∈ Finset.range (n+1), (-1)^(n-i) := by
    simp only [h1, Lagrange.interpolate_apply, Polynomial.eval_finset_sum]
    apply Finset.sum_congr s_def ?_
    intro i hi
    rw [← s_def] at hi
    have hi': i ≤ n := Finset.mem_range_succ_iff.mp hi
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [Lagrange.basis, Polynomial.eval_prod]
    simp only [s_def, r_def, Lagrange.basisDivisor, v_def, map_natCast,
    Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast]
    rw [← h4 hi']
    have: 0 < (n+1).choose i := Nat.choose_pos
      (Nat.le_add_right_of_le hi')
    rify at this
    field_simp [this]

  rw [h5]


  -- it suffices to calculate sum of (-1)^(n-i).
  -- it is 0 or 1, depends on parity of n.

  by_cases hn: Odd n
  · rw [if_pos hn]
    rcases (odd_iff_exists_bit1.mp hn) with ⟨m, rfl⟩
    clear * -
    induction' m with m ih
    · simp [Finset.sum_range_succ]
    · have h1: 2*(m+1)+1+1 = (2*m+1+1)+1+1 := by ring
      have h2: ∀ i ∈ Finset.range (2*m+1+1),
        (-1:ℝ)^(2*(m+1)+1-i) = (-1:ℝ)^(2*m+1-i) := by
        intro i hi
        simp only [Finset.mem_range] at hi
        have: 2*(m+1)+1-i = (2*m+1-i) + 2 := by omega
        simp [this, pow_add]
      rw [h1, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_congr rfl h2, ih]
      have h3: 2*(m+1)+1 - (2*m+2) = 1 := by omega
      have h4: 2*(m+1)+1 - (2*m+3) = 0 := by omega
      simp [h3, h4]

  · rw [if_neg hn]
    rw [Nat.not_odd_iff_even] at hn
    rcases (even_iff_exists_two_mul.mp hn) with ⟨m,rfl⟩
    clear * -
    induction' m with m ih
    · simp
    · have h1: 2*(m+1)+1 = (2*m+1)+1+1 := by ring
      rw [h1, Finset.sum_range_succ, Finset.sum_range_succ]
      have h2: ∀ i ∈ Finset.range (2*m+1),
        (-1:ℝ)^(2*(m+1)-i) = (-1)^(2*m-i) := by
        intro i hi
        simp only [Finset.mem_range] at hi
        have: 2*(m+1)-i = (2*m-i) + 2 := by omega
        simp [this, pow_add]
      rw [Finset.sum_congr rfl h2, ih]
      have h3: 2*(m+1) - (2*m+1) = 1 := by omega
      have h4: 2*(m+1) - (2*m+2) = 0 := by omega
      simp [h3, h4]