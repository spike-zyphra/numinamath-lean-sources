import Mathlib

/- Telescoping sum for finite sequences. -/
lemma sum_fin_sub {n : ℕ} (f : Fin (n + 1) → ℝ)
  : ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
    induction' n with h1 h2
    · norm_num
    · rw [Fin.sum_univ_succ]
      have h22 := h2 (Fin.tail f)
      simp only [Fin.tail, Fin.succ_castSucc] at h22
      rw [h22]
      norm_num

/- 12. Let $\left\{a_{n}\right\}$ be a geometric sequence with the sum of the first $n$ terms denoted as $S_{n}$, and $a_{n+1}=2 S_{n}+1\left(n \in \mathbf{N}^{*}\right)$.
(1) Find the general term formula for the sequence $\left\{a_{n}\right\}$;
(2) Insert $n$ real numbers between $a_{n}$ and $a_{n+1}$ such that these $n+2$ numbers form an arithmetic sequence with a common difference of $d_{n}$. Let the sum of the first $n$ terms of the sequence $\left\{\frac{1}{d_{n}}\right\}$ be $T_{n}$. Prove that: $T_{n}<\frac{15}{8}$. -/
theorem algebra_239028 {a : ℕ+ → ℝ} (S : ℕ+ → ℝ)
  (hS : ∀ n : ℕ+, S n = ∑ i ∈ Finset.range n, a i.succPNat)
  (ha : ∃ r, r ≠ 0 ∧ (∀ n : ℕ+, a (n + 1) = r * a n))
  (h : ∀ n : ℕ+, a (n + 1) = 2 * S n + 1) :
  (∀ n, a n = 3 ^ n.natPred)
  ∧ ((d : ℕ+ → ℝ)
    → (r : (n : ℕ+) → Fin (n + 2) → ℝ)
    → (∀ n, (r n 0 = a n ∧ r n (Fin.last (n + 1)) = a (n + 1) ∧ (∀ i : Fin (n + 1), r n i.succ - r n i.castSucc = d n )))
    → (T : ℕ+ → ℝ)
    → (∀ n : ℕ+, T n = ∑ i ∈ Finset.range n.1, (1 / d i.succPNat))
    → (∀ n, T n < (15 / 8 : ℝ))) := by

    -- First we prove the general formula a_n =  3 ^ (n - 1) (n ∈ ℕ+)
    have a_n_eq : ∀ (n : ℕ+), a n = 3 ^ n.natPred := by
      intro n

      -- we know that a is a geometric sequence
      obtain ⟨r, r_ne_zero, rh⟩ := ha

      -- when 2 ≤ n, we have a_n = 2 * S_(n - 1) + 1
      have a_n_pred_sum : ∀ n, 2 ≤ n → a n = 2 * S (n - 1) + 1 := by
        intro n nh
        convert h (n - 1)
        exact (PNat.sub_add_of_lt nh).symm

      -- so when 2 ≤ n, we have a_(n + 1) = 3 * a_n
      have eqq : ∀ n, 2 ≤ n → a (n + 1) = 3 * a n := by
        intro n nh

        -- so we have a_(n + 1) = 2 * S_n + 1
        have one := h n
        -- and a_n = 2 * S_(n - 1) + 1
        have two := a_n_pred_sum n nh

        -- subtract the equalities from eachother to get
        -- a_(n + 1) - a_n = 2 * (S_n - S_(n - 1))
        have subbed : a (n + 1) - a n = 2 * (S n - S (n - 1)) := by linarith

        -- and S_n - S_(n - 1) = a_n
        have S_sub_eq : S n - S (n - 1) = a n := by
          rw [hS n, hS (n - 1)]
          obtain ⟨n', nh'⟩ : ∃ n', n = n' + 1 := by
            exists n - 1
            exact (PNat.sub_add_of_lt nh).symm
          rw [nh']
          have add : ((n' + 1 : ℕ+) : ℕ) = n' + 1 := by norm_cast
          rw [add]
          rw [Finset.sum_range_succ]
          simp only [PNat.add_sub, add_sub_cancel_left]
          congr

        -- so a_(n + 1) - a_n = 2 * a_n
        rw [S_sub_eq] at subbed

        -- so a_(n + 1) = 3 * a_n
        linarith

      -- note that S_1 = a_1
      have S_one : S 1 = a 1 := by
        rw [hS 1]
        norm_num
        congr

      -- we have that a_2 = 2 * a_1 + 1
      have a_two : a 2 = 2 * a 1 + 1 := by
        have hue := h 1
        convert hue using 3
        exact S_one.symm

      -- then we have that the multiplier of the geometric sequence a_n is 3
      obtain ⟨rfl⟩ : r = 3 := by

        -- we have a_3 = r * a_2
        have rh_two := rh 2
        -- and a_3 = 3 * a_2
        replace eqq_two := eqq 2 (le_refl 2)

        -- so 3 * a_2 = r * a_2
        have a_2_eq_a_2 : 3 * a 2 = r * a 2 := by linarith

        -- and a_2 is not 0
        have a_2_ne_zero : a 2 ≠ 0 := by

          -- assume it's equal to 0
          by_contra eq_zero

          -- then 0 = 2 * a_1 + 1
          rw [eq_zero] at a_two

          -- so a_1 = -1 / 2
          have a_1_eq : a 1 = -1 / 2 := by linarith

          -- but we also have that a_2 = r * a_1 for some r
          have with_r : a 2 = r * a 1 := rh 1

          -- so 0 = r * (-1 / 2)
          rw [eq_zero, a_1_eq] at with_r

          -- and that means that r is 0
          have r_eq : r = 0 := by linarith

          -- but we have that r is not 0, which is a contradiction
          contradiction

        -- so r = 3
        norm_num [a_2_ne_zero] at a_2_eq_a_2
        tauto

      -- then we have that a_2 = 3 * a_1
      have a_two' : a 2 = 3 * a 1 := rh 1

      -- so a_1 = 1
      replace a_one : a 1 = 1 := by linarith

      -- then we prove a_n = 3 ^ (n - 1) by induction
      induction' n using PNat.recOn with h1 h2
      -- base case a_1 is clear
      · exact a_one
      · rw [rh, h2]
        rw [mul_comm, ←Real.rpow_natCast, ←Real.rpow_add_one]
        norm_cast
        congr
        rw [PNat.natPred_add_one]
        exact rfl
        norm_num

    -- so we're done with (1)
    refine ⟨a_n_eq, ?_⟩

    -- now we'll prove (2)
    intro d r r_eq T T_eq n

    -- we have 1 / d_n = (n + 1) / (2 * 3 ^ (n - 1))
    have d_n_eq : ∀ n, 1 / d n = (n + 1) / (2 * 3 ^ n.natPred) := by
      intro n

      -- we have that r_n is the arithmetic sequence of (n + 2) numbers
      -- where the first number is a_n and the last number is a_(n+1)
      have ⟨aa, bb, cc⟩ := r_eq n

      -- then a_(n + 1) = a_n + (n + 1) * d_n, where d_n is the common difference in the arithmetic sequence
      have a_eq : a (n + 1) = a n + (n + 1) * d n := by
        -- Telescoping sum over r_n is equal to r_n(n + 1) - r_n(0)
        have sum_one : ∑ i : Fin (n + 1), (r n i.succ - r n i.castSucc)
          = r n (Fin.last (n + 1)) - r n 0 := sum_fin_sub (r n)

        -- but it's also equal to (n + 1) * d_n
        have sum_two : ∑ i : Fin (n + 1), (r n i.succ - r n i.castSucc) = (n + 1) * d n := by
          -- because every difference is equal to d_n
          simp only [cc]
          norm_num

        -- combining equalties and re-ordering proves
        -- a_(n + 1) = a_n + (n + 1) * d_n
        linarith

      -- the difference between consecutive a_n is 2 * 3 ^ (n - 1)
      have sub_eq : a (n + 1) - a n = 2 * 3 ^ n.natPred := by
        have pred_add : (n + 1).natPred = n.natPred + 1 := by
          simp only [PNat.natPred_add_one]
          exact rfl
        simp only [a_n_eq, pred_add, pow_add, ←mul_sub_one]
        ring

      -- we also get that a_(n + 1) - a_n is not 0
      have a_sub_ne_zero : a (n + 1) - a n ≠ 0 := by
        rw [sub_eq]
        norm_num

      -- i.e. consecutive values of a_n are not equal
      have a_succ_ne : a (n + 1) ≠ a n := sub_ne_zero.mp a_sub_ne_zero

      -- d_n is not equal to 0
      have d_ne_zero : d n ≠ 0 := by
        -- assume opposite
        by_contra eq_zero
        -- then a_(n + 1) = a_n
        have eqq : a (n + 1) = a n := by
          rw [eq_zero] at a_eq
          simpa only [mul_zero, add_zero] using a_eq

        -- but we just proved the opposite
        contradiction

      -- because terms are non-zero, we have
      -- 1 / d_n = (n + 1) / (a_(n + 1) - a_n)
      have d_n_eq : 1 / d n = (n + 1) / (a (n + 1) - a n) := by
        field_simp
        linarith

      -- using a_(n + 1) - a_n = 2 * 3 ^ (n - 1) we get the desired result
      rw [sub_eq] at d_n_eq
      exact d_n_eq

    -- now that we have an expression for d_n we can write expressions for T_n

    -- we have 2 * T_n = ∑ i < n, ((i + 2) / 3 ^ i)
    have two_T : 2 * T n = ∑ i ∈ Finset.range n, ((i + 2 : ℝ) / 3 ^ i) := by
      rw [T_eq]
      simp only [d_n_eq, Finset.mul_sum]
      congr
      ext i
      field_simp
      norm_cast
      ring

    -- we have 2 * T_n / 3 = ∑ i < n, ((i + 2) / 3 ^ (i + 1))
    have two_third_T : 2 * T n / 3 = ∑ i ∈ Finset.range n, (((i + 1 : ℕ) + 1 : ℝ) / 3 ^ (i + 1)) := by
      rw [two_T, Finset.sum_div]
      congr
      ext i
      field_simp
      norm_cast

    -- consider the positive natural number n as n' + 1 for some natural number (which may be 0)
    have ⟨n', nh⟩ : ∃ n' : ℕ, n = n' + 1 := by
      exists n.natPred
      norm_num

    -- use n' in sums
    rw [nh] at two_third_T two_T

    -- we have that 4 * T_n / 3 = 2 * T_n - 2 * T_n / 3
    have four_thirds_T : 4 * T n / 3 = 2 * T n - 2 * T n / 3 := by linarith

    -- write RHS as sums
    rw [two_third_T, two_T] at four_thirds_T

    -- separate first value of first sum, and last value of second sum
    have sums_eq : ∑ i ∈ Finset.range (n' + 1), (i + 2 : ℝ) / 3 ^ i - ∑ i ∈ Finset.range (n' + 1), (((i + 1 : ℕ) + 1 : ℝ) / 3 ^ (i + 1))
      = 2 +
        (∑ x ∈ Finset.range n', (x + 1 + 2 : ℝ) / 3 ^ (x + 1) - ∑ x ∈ Finset.range n', (x + 1 + 1 : ℝ) / 3 ^ (x + 1)
        - (↑n' + 1 + 1) / 3 ^ (n' + 1))
      := by
        nth_rw 2 [Finset.sum_range_succ]
        have lee : 1 ≤ n' + 1 := by linarith
        simp_rw [←Finset.sum_range_add_sum_Ico _ lee]

        have as_offset : Finset.Ico 1 (n' + 1) = Finset.Ico (0 + 1) (n' + 1) := by norm_num

        simp_rw [as_offset, ←Finset.sum_Ico_add']
        simp only [Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero, zero_add, pow_zero,
          div_one, Nat.Ico_zero_eq_range, Nat.cast_add, Nat.cast_one]
        rw [add_sub_assoc, ←sub_sub]

    rw [sums_eq] at four_thirds_T


    -- then we combine the sums
    rw [←Finset.sum_sub_distrib] at four_thirds_T

    -- simplify the sum
    have sum_eq : ∑ x ∈ Finset.range n', (((x : ℝ) + 1 + 2) / 3 ^ (x + 1) - ((x : ℝ) + 1 + 1) / 3 ^ (x + 1))
      = ∑ x ∈ Finset.range n', (1 / 3 ^ (x + 1)) := by
        congr
        ext i
        norm_num
        ring_nf

    rw [sum_eq] at four_thirds_T

    -- ∑ x < n', 1 / 3 ^ (x + 1) is a sum over a geometric sequence, so it has a closed form
    have geom_sum : ∑ x ∈ Finset.range n', (1 : ℝ) / 3 ^ (x + 1) = (1 / 3) * (1 - (1 / 3 ^ n')) / (1 - (1 / 3)) := by
      convert_to ∑ x ∈ Finset.range ((n' + 1) - 1), (1 / 3 : ℝ) ^ (1 + x) = _
      · norm_num
        congr
        ext i
        ring_nf

      -- write as ∑ i ∈ (1, n'], x ^ i instead of ∑ i ∈ [0, n'), x ^ (i + 1)
      rw [←Finset.sum_Ico_eq_sum_range]
      have one_le : 1 ≤ n' + 1 := by omega

      -- then (∑ i ∈ (1, n'], (1 / 3) ^ i) * (1 - 1 / 3) = (1 / 3) ^ 1 - (1 / 3) ^ (n' + 1)
      have geom_equality := geom_sum_Ico_mul_neg (1 / 3 : ℝ) one_le

      -- normalize the equality
      field_simp at geom_equality ⊢
      ring_nf at geom_equality ⊢
      linarith

    rw [geom_sum] at four_thirds_T

    -- simplify
    field_simp at four_thirds_T
    ring_nf at four_thirds_T

    -- so we have a simple expression for T_n
    -- T_n = (3 ^ (n' * 2) * 135) / ((3 ^ (n' * 2)) * 72) - (3 ^ n' * ((n' * 18) + 63)) / (3 ^ (n' * 2) * 72)
    have T_n_eq : T n
      = (3 ^ (n' * 2) * 135) / ((3 ^ (n' * 2)) * 72) - (3 ^ n' * ((n' * 18) + 63)) / (3 ^ (n' * 2) * 72)
      := by
        field_simp
        linarith

    -- the left term is equal to 15 / 8
    have left_term : (3 ^ (n' * 2) * 135 : ℝ) / ((3 ^ (n' * 2)) * 72)
      = 15 / 8 := by
        field_simp
        ring
    rw [left_term] at T_n_eq

    -- the right term is equal to (((n' + 1) * 2) + 5) / (3 ^ n' * 8)
    have right_term : (3 ^ n' * ((n' * 18) + 63) : ℝ) / (3 ^ (n' * 2) * 72)
      = ((((n' + 1) * 2) + 5) : ℝ) / (3 ^ n' * 8) := by
        field_simp
        ring

    rw [right_term] at T_n_eq

    -- so we want to prove 15 / 8 - ((n' + 1) * 2 + 5) / (3 ^ n' * 8) < 15 / 8
    rw [T_n_eq]

    -- the inequality is clearly true
    norm_num
    positivity