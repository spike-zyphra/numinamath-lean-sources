import Mathlib

open Real

/- Suppose $p$ and $q$ are two different positive integers and $x$ is a real number. Form the product $(x+p)(x+q)$. (a) Find the sum $S(x, n)=\sum(x+p)(x+q)$, where $p$ and $q$ take values from 1 to $n$. -/
theorem imo_24705_a
    (S : ℝ → ℕ → ℝ)
    (h_defS : ∀ x : ℝ, ∀ n : ℕ, S x n = ∑ p ∈ Finset.Icc 1 n, (∑ q ∈ (Finset.Icc 1 n \ {p}), (x + p) * (x + q))) :
    ∀ x n, S x n = n * (n - 1) * (x ^ 2 + (n + 1) * x + (n + 1) * (3 * n + 2) / 12) := by

  intro x n

  rcases Nat.eq_zero_or_pos n with hn | hn

  -- if n = 0, it's easy to verify
  . norm_num [h_defS, hn]

  -- if n > 0
  calc S x n
    _ = ∑ p ∈ Finset.Icc 1 n, (∑ q ∈ (Finset.Icc 1 n \ {p}), (x ^ 2 + (p + q) * x + p * q)) := by
      rw [h_defS]
      congr; ext p
      congr; ext q
      ring_nf
    _ = (∑ p ∈ Finset.Icc 1 n, (∑ q ∈ (Finset.Icc 1 n \ {p}), (x ^ 2))) +
        (∑ p ∈ Finset.Icc 1 n, (∑ q ∈ (Finset.Icc 1 n \ {p}), (p + q) * x)) +
        (∑ p ∈ Finset.Icc 1 n, (∑ q ∈ (Finset.Icc 1 n \ {p}), p * q)) := by
      simp_rw [Finset.sum_add_distrib]
      norm_cast
    _ = n * (n - 1) * (x ^ 2 + (n + 1) * x + (n + 1) * (3 * n + 2) / 12) := by

      -- lemma, split [1, n] \ {p} into [1, p-1] ∪ [p+1, n]
      have l1 : ∀ p ∈ Finset.Icc 1 n, (Finset.Icc 1 n \ {p}) = Finset.Icc 1 (p - 1) ∪ Finset.Icc (p + 1) n := by
        intro p hp
        apply Finset.Subset.antisymm
        . apply Finset.subset_iff.mpr ?_
          intro x hx
          simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_singleton] at hx
          simp
          omega
        . apply Finset.subset_iff.mpr ?_
          intro x hx
          simp only [Finset.mem_union, Finset.mem_Icc] at hx hp
          simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_singleton]
          rcases hx <;> omega

      -- lemma, [1, p-1] and [p+1, n] ard disjoint
      have l2 : ∀ p ∈ Finset.Icc 1 n, Disjoint (Finset.Icc 1 (p - 1)) (Finset.Icc (p + 1) n) := by
        intro p hp
        refine Finset.disjoint_left.mpr ?_
        intro x hx
        rw [Finset.mem_Icc] at hp hx
        rw [Finset.mem_Icc]
        omega

      -- lemma, ([1, n] \ {p}).card = n - 1
      have l3 : ∀ p ∈ Finset.Icc 1 n, (Finset.Icc 1 n \ {p}).card = n - 1 := by
        intro p hp
        rw [l1 p hp,
            Finset.card_union_of_disjoint (l2 p hp),
            Nat.card_Icc, Nat.card_Icc]
        obtain ⟨hp1, hp2⟩ := Finset.mem_Icc.mp hp
        omega

      -- lemma, ∑ x ∈ Finset.Icc 1 n, x = n * (n + 1) / 2
      have l4' : ∑ x ∈ Finset.Icc 1 n, x = n * (n + 1) / 2 := by
        calc
          _ = ∑ x ∈ Finset.Icc 0 n, x - 0 := by
            exact Nat.eq_sub_of_add_eq' rfl
          _ = ∑ x ∈ Finset.range (n + 1), x - 0 := by
            congr
            rw [Finset.range_eq_Ico]
            rfl
          _ = n * (n + 1) / 2 := by
            rw [Finset.sum_range_id, Nat.add_sub_cancel, mul_comm, tsub_zero]

      -- lemma, Real type version of l4'
      have l4 : ∑ x ∈ Finset.Icc 1 n, (x:ℝ) = n * (n + 1) / (2:ℝ) := by
        rify at l4'
        rw [l4']
        rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
        . rw [hk]
          rify
          rw [← two_mul, mul_assoc, mul_div_cancel_left₀ _ two_ne_zero,
              ← two_mul, mul_assoc, mul_div_cancel_left₀ _ two_ne_zero]
          norm_cast
        . rw [hk]
          rify
          rw [show 2 * (k:ℤ) + 1 + 1 = 2 * (k + 1) by ring,
              mul_comm 2 ((k : ℤ) + 1), ← mul_assoc, Int.mul_ediv_cancel _ two_ne_zero,
              show 2 * (k:ℝ) + 1 + 1 = 2 * (k + 1) by ring,
              mul_div_assoc, mul_div_cancel_left₀ _ two_ne_zero]
          norm_cast

      -- lemma, ∑ x ∈ Finset.Icc 1 n \ {p}, x = n * (n + 1) / 2 - p
      have l5 : ∀ p ∈ Finset.Icc 1 n, ∑ x ∈ Finset.Icc 1 n \ {p}, (x:ℝ) = n * (n + 1) / (2:ℝ) - p := by
        intro p hp
        calc ∑ x ∈ Finset.Icc 1 n \ {p}, (x:ℝ)
          _ = ∑ x ∈ Finset.Icc 1 n, x - p := by
            rw [Finset.sum_eq_sum_diff_singleton_add hp, Nat.cast_add, Nat.cast_sum, add_sub_cancel_right]
          _ = n * (n + 1) / (2:ℝ) - p := by
            rw [Nat.cast_sum, l4]

      -- lemma, sum of square, $\sum_{1 \le x \le n} x ^ 2 = \frac{n (n + 1) *(2n + 1)}{6}$
      have l6 : ∑ x ∈ Finset.Icc 1 n, (x : ℝ) ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
        have : ∀ m, ∑ x ∈ Finset.range m, (x : ℝ) ^ 2 = (m - 1) * m * (2 * m - 1) / 6 := by
          intro m
          induction m with
          | zero => norm_num
          | succ m ih =>
            rw [Finset.sum_range_succ, ih, Nat.cast_add, Nat.cast_one]
            ring_nf
        convert this (n + 1) using 1
        . have : 0 < n + 1 := by exact Nat.add_pos_left hn 1
          rw [Finset.sum_range_eq_add_Ico _ this, Nat.cast_zero, zero_pow two_ne_zero, zero_add]
          rfl
        . rw [Nat.cast_add, Nat.cast_one, mul_add]
          ring_nf

      -- first part of the expression, \sum_{1 \le p \ne q \le n} x ^ 2 = n  (n - 1) x ^ 2
      have r1 : ∑ p ∈ Finset.Icc 1 n, (∑ q ∈ (Finset.Icc 1 n \ {p}), (x ^ 2))
          = n * (n - 1) * x ^ 2 := by
        calc ∑ p ∈ Finset.Icc 1 n, (∑ q ∈ (Finset.Icc 1 n \ {p}), (x ^ 2))
          _ = ∑ p ∈ Finset.Icc 1 n, (n - 1) * x ^ 2 := by
            conv =>
              lhs
              simp only [Finset.sum_const, nsmul_eq_mul]
            apply Finset.sum_congr rfl
            intro p hp
            rw [l3 p hp, Nat.cast_sub (by exact hn), Nat.cast_one]
          _ = n * (n - 1) * x ^ 2 := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
            ring

      -- second part of the expression, $\sum_{1 \le p \ne q \le n} (p + q)x = n  (n - 1) ((n + 1)x)$
      have r2 : ∑ p ∈ Finset.Icc 1 n, (∑ q ∈ (Finset.Icc 1 n \ {p}), (p + q) * x)
          = n * (n - 1) * ((n + 1) * x) := by
        calc
          _ = ((∑ p ∈ Finset.Icc 1 n, (∑ q ∈ (Finset.Icc 1 n \ {p}), p)) + (∑ p ∈ Finset.Icc 1 n, (∑ q ∈ (Finset.Icc 1 n \ {p}), q))) * x := by
            simp_rw [← Finset.sum_mul, Finset.sum_add_distrib]
            rify
          _ = ((∑ x ∈ Finset.Icc 1 n, (n - 1) * x) + (∑ p ∈ Finset.Icc 1 n, ∑ q ∈ Finset.Icc 1 n \ {p}, q)) * x := by
            simp only [Finset.sum_const, smul_eq_mul]
            congr 3
            apply Finset.sum_congr rfl
            intro p hp
            rw [l3 p hp]
          _ = n * (n - 1) * ((n + 1) * x) := by
            have : ∑ p ∈ Finset.Icc 1 n, ∑ q ∈ Finset.Icc 1 n \ {p}, q = n * (n + 1) * (n - 1) / (2:ℝ) := by
              trans ∑ p ∈ Finset.Icc 1 n, (n * (n + 1) / (2:ℝ) - p)
              . rw [Nat.cast_sum]
                apply Finset.sum_congr rfl
                intro p hp
                convert l5 p hp
                rw [Nat.cast_sum]
              . rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, l4]
                ring_nf
                field_simp
                ring_nf
            rw [← Finset.mul_sum, Nat.cast_mul, Nat.cast_sum, l4, this]
            ring_nf
            field_simp
            ring_nf

      -- third part of the expression, $\sum_{1 \le p \ne q \le n} pq = n  (n - 1) ((n+1)(3n+2)/12)$
      have r3 : ∑ p ∈ Finset.Icc 1 n, (∑ q ∈ (Finset.Icc 1 n \ {p}), (p:ℝ) * q)
          = n * (n - 1) * ((n + 1) * (3 * n + 2) / (12 : ℝ)) := by

        calc (∑ p ∈ Finset.Icc 1 n, (∑ q ∈ (Finset.Icc 1 n \ {p}), (p:ℝ) * q))
          _ = ∑ p ∈ Finset.Icc 1 n, (p * (∑ q ∈ (Finset.Icc 1 n \ {p}), (q:ℝ))) := by
            simp_rw [← Finset.mul_sum]
          _ = ∑ p ∈ Finset.Icc 1 n, (p * ((n:ℝ) * (n + 1) / 2 - p)) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [l5 p hp]
          _ = (∑ p ∈ Finset.Icc 1 n, (p:ℝ)) * ((n:ℝ) * (n + 1) / 2) - (∑ p ∈ Finset.Icc 1 n, (p:ℝ) ^ 2) := by
            simp_rw [mul_sub, ← pow_two, Finset.sum_sub_distrib, ← Finset.sum_mul]
          _ = n * (n - 1) * ((n + 1) * (3 * n + 2) / (12 : ℝ)) := by
            rw [l4, l6]
            ring_nf

      -- it can be proved by combining r1, r2 and r3
      rify
      rw [r1, r2, r3]
      ring






/- Suppose $p$ and $q$ are two different positive integers and $x$ is a real number. Form the product $(x+p)(x+q)$. (b) Do there exist integer values of $x$ for which $S(x, n)=0$ ? -/
theorem imo_24705_b
    (S : ℝ → ℕ → ℝ)
    (h_defS : ∀ x : ℝ, ∀ n : ℕ, S x n = ∑ p ∈ Finset.Icc 1 n, (∑ q ∈ (Finset.Icc 1 n \ {p}), (x + p) * (x + q))) :
    ∀ n > 0, ((∃ x : ℤ, S x n = 0) ↔ (n = 1 ∨ ∃ k : ℕ, n = 3 * k ^ 2 - 1)) := by

  -- lemma, the two roots of quadratic function
  have l_quadratic_eq_zero_iff {a b c : ℝ} (ha : a ≠ 0) (h : 0 ≤ discrim a b c) (x : ℝ) :
      a * x ^ 2 + b * x + c = 0 ↔
      x = (-b + Real.sqrt (discrim a b c)) / (2 * a) ∨
      x = (-b - Real.sqrt (discrim a b c)) / (2 * a) := by
    let d := Real.sqrt <| discrim a b c
    have : discrim a b c = d * d := Eq.symm <| mul_self_sqrt h
    convert quadratic_eq_zero_iff ha this x using 1
    ring_nf


  intro n h_npos

  -- If n = 1
  have : n = 1 ∨ n > 1 := by exact LE.le.eq_or_gt h_npos
  rcases this with h_neqone | h_ngtone
  . simp [h_neqone, h_defS]

  -- Otherwise n > 1

  -- prop, (n + 1) / 3 is positive
  have h_gt : 0 < ((n : ℝ) + 1) / 3 := by
    exact div_pos (Nat.cast_add_one_pos n) three_pos

  -- it is easy to see that the equation $S(x, n)=0$ has two roots $x_{1,2}=$ $(-(n+1) \pm \sqrt{(n+1) / 3}) / 2$.
  have r1 (x : ℝ) : S x n = 0 ↔ (x = (-(n + 1) + √((n + 1) / 3)) / 2 ∨ x = (-(n + 1) - √((n + 1) / 3)) / 2) := by

    -- convert S x n into a quadratic function according to question a
    have t1 : S x n = 0 ↔ (x ^ 2 + (n + 1) * x + (n + 1) * (3 * n + 2) / 12) = 0 := by
      rw [imo_24705_a S h_defS _ n]
      simp only [mul_eq_zero, Nat.cast_eq_zero, or_iff_right_iff_imp]
      intro h
      rify at h_ngtone
      rcases h <;> linarith

    -- use the 'quadratic_eq_zero_iff' lemma to get two roots of the euqdratic function
    have t2 : x ^ 2 + (n + 1) * x + (n + 1) * (3 * n + 2) / 12 = 0 ↔ x = (-(n + 1) + √((n + 1) / 3)) / 2 ∨ x = (-(n + 1) - √((n + 1) / 3)) / 2 := by
      rw [← one_mul (x ^ 2)]

      -- to use the 'quadratic_eq_zero_iff' lemma, we define the coefficients of the quadratic function
      let a : ℝ := 1
      let b : ℝ := (n + 1)
      let c : ℝ := (n + 1) * (3 * n + 2) / 12

      -- check a ≠ 0
      have h_a_nezero : a ≠ 0 := by norm_num

      -- calculate discriminant of the quadratic function
      have h_discrim : discrim a b c = (n + 1) / 3 := by
        dsimp [discrim, a, b, c]
        ring_nf

      -- check discriminant is nonnegative
      have h_discrim_nonneg : 0 ≤ discrim a b c := by
        apply le_of_lt
        rw [h_discrim]
        exact h_gt

      -- use the 'quadratic_eq_zero_iff' lemma, we get two roots of the quadratic function
      convert l_quadratic_eq_zero_iff h_a_nezero h_discrim_nonneg x using 1
      simp [a, b, c, h_discrim]

    simp only [t1, t2, neg_add_rev, Nat.ofNat_nonneg, sqrt_div']


  -- If S x n = 0, and x is an integer, then (n + 1) / 3 equals to square of a natural number
  have r2 (x : ℤ) : (S x n = 0) → ∃ k : ℕ, k ^ 2 = (((n : ℝ) + 1) / 3) := by

    -- (S x n = 0) → (∃ k, k ^ 2 = ((n + 1) / 3))
    intro h

    -- lemma about type conversion
    have l_tmp (f : ℤ → Prop) (h : ∃ k : ℤ, k ≥ 0 ∧ f k) : ∃ n : ℕ, f n := by
      obtain ⟨k, ⟨hknonneg, hk⟩⟩ := h
      use k.natAbs
      convert hk
      omega

    apply l_tmp (fun t => t ^ 2 = ((n : ℝ) + 1) / 3) _

    -- use r1 to convert S x n into two roots
    rcases (r1 x).mp h with hx | hx

    . -- reform the equation, putting sqrt at one side
      have : √((n + 1) / 3) = 2 * x + (n + 1) := by linarith
      apply_fun fun t => t ^ 2 at this
      rw [sq_sqrt (le_of_lt h_gt)] at this
      use (2 * x + (n + 1)).natAbs
      have tt := Int.natAbs_pow_two (2 * x + (n + 1))
      rify at tt
      rw [this, ← tt]
      simp only [Int.natCast_natAbs, abs_nonneg, Int.cast_abs, Int.cast_add, Int.cast_mul,
        Int.cast_ofNat, Int.cast_natCast, Int.cast_one, sq_abs, and_self]

    . -- reform the equation, putting sqrt at one side
      have : √((n + 1) / 3) = -(2 * x + (n + 1)) := by linarith
      apply_fun fun t => t ^ 2 at this
      rw [sq_sqrt (le_of_lt h_gt), neg_sq] at this
      use (2 * x + (n + 1)).natAbs
      have tt := Int.natAbs_pow_two (2 * x + (n + 1))
      rify at tt
      rw [this, ← tt]
      simp only [Int.natCast_natAbs, abs_nonneg, Int.cast_abs, Int.cast_add, Int.cast_mul,
        Int.cast_ofNat, Int.cast_natCast, Int.cast_one, sq_abs, and_self]


  constructor
  . intro ⟨x, h⟩
    right
    -- use r2
    obtain ⟨k, hk⟩ := r2 x h
    -- k is positive
    have h_kpos : k > 0 := by
      by_contra! h_contra
      interval_cases k
      norm_num at hk
      linarith only [hk, h_gt]
    have h_le : 1 ≤ 3 * k ^ 2 := by
      have : 1 ≤ k ^ 2 := by exact Nat.one_le_pow 2 k h_kpos
      linarith only [this]
    use k
    rify
    rw [Nat.cast_sub h_le, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    linarith
  . intro h
    simp only [show n ≠ 1 by linarith, false_or] at h
    obtain ⟨k, hk⟩ := h

    -- k is positive
    have h_kpos : k > 0 := by
      by_contra! h_contra
      interval_cases k
      norm_num at hk
      linarith only [h_npos, hk]
    have h_le : 1 ≤ 3 * k ^ 2 := by
      have : 1 ≤ k ^ 2 := by exact Nat.one_le_pow 2 k h_kpos
      linarith only [this]

    set x : ℤ := k * (1 - 3 * k) / 2 with hx
    use x
    apply (r1 x).mpr
    left

    -- k * （1 - 3 * k）is divided by 2
    have h_dvd2 : (2 : ℤ) ∣ k * (1 - 3 * k) := by
      rcases k.even_or_odd with h_keven | ⟨t, ht⟩
      . have t1 : 2 ∣ k := by exact even_iff_two_dvd.mp h_keven
        have t2 : (2 : ℤ) ∣ k := by exact Int.ofNat_dvd_right.mpr t1
        exact Dvd.dvd.mul_right t2 (1 - 3 * ↑k)
      . have t1 : (2 : ℤ) ∣ (1 - 3 * k) := by
          rw [ht, Nat.cast_add, Nat.cast_mul, Nat.cast_two, Nat.cast_one,
              show 1 - 3 * (2 * (t : ℤ) + 1) = 2 * (-3 * t - 1) by ring]
          exact Int.dvd_mul_right 2 (-3 * ↑t - 1)
        exact Dvd.dvd.mul_left t1 ↑k

    -- calculate (-(n + 1) + √((n + 1) / 3)) / 2
    have h_eq : (-(n + 1) + √((n + 1) / 3)) / 2 = (- 3 * k ^ 2 + k) / 2 := by
      rw [hk, Nat.cast_sub h_le, Nat.cast_one, sub_add_cancel,
          Nat.cast_mul, Nat.cast_ofNat, mul_div_cancel_left₀ _ three_ne_zero,
          Nat.cast_pow, sqrt_sq (Nat.cast_nonneg' k)]
      ring_nf

    rw [h_eq, hx, Int.cast_div h_dvd2 two_ne_zero, Int.cast_mul, Int.cast_sub, Int.cast_mul,
        Int.cast_one, Int.cast_three, Int.cast_two]

    congr
    ring_nf
    norm_cast
