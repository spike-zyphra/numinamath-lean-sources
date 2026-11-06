import Mathlib

open Finset Real

/- Variant of Cauchy-Schwarz inequality for positive elements: sum of sequence times sum of inverse of sequence,
  is larger than the square of the sequence length. -/
lemma Fin_Real_cauchy_inv_of_pos {n : ℕ} {f : Fin n → ℝ} (hf : ∀ i, 0 < f i)
  : n ^ 2 ≤ (∑ i : Fin n, f i) * (∑ i : Fin n, (f i)⁻¹) := by
    -- every element is non-negative
    have all_le := (le_of_lt <| hf ·)

    -- invoke cauchy
    have cauchy := @Real.sum_sqrt_mul_sqrt_le _ f (Inv.inv ∘ f) Finset.univ
      all_le
      (by simpa only [Function.comp_apply, inv_nonneg] using all_le)

    -- √f_i * √((f i)⁻¹) = 1
    have lee : ∀ i, √(f i) * √((Inv.inv ∘ f) i) = 1 := by
      intro i
      rw [←Real.sqrt_mul (all_le i)]
      norm_num
      have f_i_ne_zero : f i ≠ 0 := (ne_of_lt (hf i)).symm
      field_simp

    simp_rw [lee] at cauchy
    norm_num at cauchy

    -- squaring both sides we have our inequality
    convert (sq_le_sq₀ (by linarith) (by positivity)).mpr cauchy

    -- every term is nonnegative
    have pos : 0 ≤ (∑ i : Fin n, f i) := Fintype.sum_nonneg all_le
    have pos_f_inv : ∀ (x : Fin n), 0 ≤ (f x)⁻¹ := by norm_num [all_le]
    have pos_inv : 0 ≤ (∑ i : Fin n, (f i)⁻¹) := Fintype.sum_nonneg pos_f_inv

    -- simplify
    rw [←Real.sqrt_mul pos, Real.sq_sqrt]

    -- operations were valid, because every term is positive
    positivity

/- Sum over [1, k + 1] is equal to sum over [0, k + 2). -/
lemma Finset_sum_icc_one_id (k : ℕ) : ∑ x ∈ Icc 1 (k + 1), x = ∑ x ∈ range (k + 2), x
  := by
    induction' k with h1 h2
    · decide
    · rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top, h2]
      omega

/- 10. (2002 First Women's Mathematical Olympiad) Let $P_{1}, P_{2}, \cdots, P_{n}(n \geqslant 2)$ be any permutation of $1,2, \cdots, n$. Prove that:

$$

\frac{1}{P_{1}+P_{2}}+\frac{1}{P_{2}+P_{3}}+\cdots+\frac{1}{P_{n-2}+P_{n-1}}+\frac{1}{P_{n-1}+P_{n}}>\frac{n-1}{n+2} .

$$
 -/
theorem inequalities_173899 {n : ℕ} (hn : n ≥ 2) (P : Equiv.Perm ℕ)
    (hP : ∀ i, (i ∈ Icc 1 n ↔ P i ∈ Icc 1 n)) :
    ∑ i ∈ Icc 1 (n - 1), (1 / ((P i + P (i + 1)) : ℝ)) > (n - 1) / (n + 2)
  := by
    -- simplify, use < instead of >
    simp only [one_div, gt_iff_lt]

    -- n is positive, so we replace it with n + 1
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := by
      exists n - 1
      omega

    -- let f be P_(i + 1) + P_(i + 2)
    let f : Fin n → ℕ := fun i => P (i + 1) + P (i + 2)

    -- f is always positive
    have f_pos : ∀ i, 0 < f i := by
      intro i
      unfold f
      simp only [add_pos_iff]

      have p_one_mem : P (i + 1) ∈ Icc 1 (n + 1) := by
        apply (hP (i + 1)).mp
        norm_num

      refine Or.inl ?_

      simp only [mem_Icc] at p_one_mem
      omega

    -- let f' be the same as f but considered as real numbers
    let f' : Fin n → ℝ := Nat.cast ∘ f

    -- f' is also positive
    have f'_pos : ∀ i, 0 < f' i := by
      norm_num [f']
      exact f_pos

    -- then we use Cauchy-Schwarz to get n ^ 2 ≤ (∑ f' i) * ∑ i (f' i)⁻¹
    have cauchy := Fin_Real_cauchy_inv_of_pos f'_pos

    -- rearrange to get n ^ 2 / ∑ f' i ≤ ∑ (f' i)⁻¹
    rw [mul_comm, ←div_le_iff₀] at cauchy

    -- simplify
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, add_tsub_cancel_right]

    -- RHS is equal to the upper bound we got from Cauchy-Schwarz
    convert lt_of_lt_of_le ?_ cauchy
    · unfold f' f
      simp only [Function.comp_apply, Nat.cast_add]
      norm_cast
      -- the sums are equal because we have a bijective function between the terms
      refine sum_bij ?_ ?_ ?_ ?_ ?_
      -- map from [1, n] to Fin n
      · intro a ah
        refine ⟨a - 1, ?_⟩
        simp only [mem_Icc] at ah
        omega
      · norm_num
      -- it's injective
      · intro a ah b bh eq
        simp only [Fin.mk.injEq, mem_Icc] at eq ah bh
        omega
      -- it's surjective
      · intro b bh
        exists b + 1
        norm_num
        omega
      -- the terms are equal
      · intro a ah
        simp at ah
        norm_num
        have sub_add : a - 1 + 1 = a := by omega
        have sub_add' : a - 1 + 2 = a + 1 := by omega
        rw [sub_add, sub_add']

    -- simplify sum, consider as sum over natural numbers
    unfold f'
    simp only [Function.comp_apply]
    rw [←Nat.cast_sum]

    -- expand sum over f
    have sum_eq : ∑ x : Fin n, f x = 2 * (∑ x ∈ Icc 1 (n + 1), P x) - P 1 - P (n + 1) := by

      -- we can consider sums over Fin n as sums over range
      have as_range := @Finset.sum_range _ _ n (fun i : ℕ => P (i + 1) + P ((i + 1) + 1))

      -- expand and split sum
      rw [←as_range, Finset.sum_add_distrib, Finset.range_eq_Ico, Finset.sum_Ico_add',
        Finset.sum_Ico_add' (fun i => P (i + 1)), Finset.sum_Ico_add']

      -- simplify
      simp only [zero_add, Nat.reduceAdd]

      -- Add P_1 + P_(n + 1) to both sides
      suffices : (∑ x ∈ Ico 1 (n + 1), P x + P (n + 1)) + (P 1 + ∑ x ∈ Ico 2 (n + 2), P x) = 2 * ∑ x ∈ Icc 1 (n + 1), P x - P 1 - P (n + 1) + P 1 + P (n + 1)
      · linarith

      -- we can merge top term
      have eq_top : ∑ x ∈ Ico 1 (n + 1), P x + P (n + 1)
        = ∑ x ∈ Ico 1 (n + 2), P x := by
          refine (sum_Ico_succ_top ?_ P).symm
          omega

      -- we can merge bottom term
      have eq_bot : P 1 + ∑ x ∈ Ico 2 (n + 2), P x
        = ∑ x ∈ Ico 1 (n + 2), P x := rfl
      -- merge
      rw [eq_top, eq_bot]

      -- simplify
      ring_nf

      -- group similar terms
      rw [Nat.sub_sub, add_assoc]

      -- we have a = a - b + b, because b ≤ a
      refine Nat.eq_add_of_sub_eq ?_ ?_
      · convert_to _ ≤ (∑ x ∈ Ico 1 (n + 2), P x) * 2
        · ring_nf
        -- seperate terms from sum
        rw [←eq_bot, sum_Ico_succ_top ?_ P]

        ring_nf
        omega
        · omega

      -- sums are over the same set
      -- because [1, 2 + n) = [1, 1 + n]
      · congr 3
        ext i
        norm_num
        omega
    rw [sum_eq]

    -- sum over all P values is the same as sum over first n + 1 naturals
    -- because P is a permutation of first naturals
    have sum_eq : ∑ x ∈ Icc 1 (n + 1), P x = ∑ x ∈ Icc 1 (n + 1), x := by
      refine sum_equiv P ?_ (by norm_num)
      intro i
      -- P is bijective on [1, n + 1]
      exact hP i

    rw [sum_eq]

    -- we have a simple bound on the denominator on the RHS
    have denom_le : 2 * ∑ x ∈ Icc 1 (n + 1), x - P 1 - P (n + 1)
      ≤ (n + 1) * (n + 2) - 3 := by
        -- simplify, move terms to RHS
        norm_num

        -- simplify using Gauss' summation formula
        rw [Finset_sum_icc_one_id n, mul_comm 2, Finset.sum_range_id_mul_two]
        ring_nf

        have lhs_eq : n * (2 + n - 1) + (2 + n - 1) * 2
          = n * (2 + n - 1) + (4 + 2 * n - 2) := by omega

        rw [lhs_eq, Nat.mul_sub, mul_one, mul_add]

        have cancel_sub : n * 2 + n * n - n = n + n * n := by omega

        rw [cancel_sub]

        convert_to n * n + (4 + 3 * n - 2) ≤ _
        · omega
        rw [←pow_two]

        -- n is positive, so consider it as n + 1
        obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := by
          exists n - 1
          omega
        ring_nf

        -- seperate common terms on both sides
        convert_to (n ^ 2 + n * 5 + 3) + 3 ≤ (n ^ 2 + n * 5 + 3) + (P (2 + n) + P 1)
        · omega
        · omega

        -- cancel common terms, then we just need to show that 3 ≤ P_(2 + n) + P_1
        gcongr

        -- P_(2 + n) is positive
        have left_pos : 1 ≤ P (2 + n) := by
          have app := (hP (2 + n)).mp
          norm_num at app
          exact (app (by omega) (by omega)).1

        -- P_1 is positive
        have right_pos : 1 ≤ P 1 := by
          have app := (hP 1).mp
          norm_num at app
          exact app.1

        -- and they are not equal
        have not_eq : P (2 + n) ≠ P 1 := by
          have inj : Function.Injective P := Equiv.injective P
          apply (@inj (2 + n) 1).mt
          omega

        -- so the sum is at least 3
        omega

    -- so we get a lower bound on the RHS
    have le_rhs : (n : ℝ) ^ 2 / (((n + 1) * (n + 2) - 3 : ℕ) : ℝ)
      ≤ (n : ℝ) ^ 2 / (2 * ∑ x ∈ Icc 1 (n + 1), x - P 1 - P (n + 1) : ℕ)
        := by
        -- to prove a / b ≤ a / d, we just need to show that d ≤ b
        -- given that everything is positive
        rw [div_le_div_iff_of_pos_left]
        -- we proved the d ≤ b bound earlier
        · norm_cast

        -- n ^ 2 is positive
        · norm_cast
          have n_pos : 0 < n := by omega
          positivity
        -- (n + 1) * (n + 2) - 3 is positive
        · norm_cast
          ring_nf
          omega
        -- 2 * ∑ x ∈ [1, n + 1], x - P_1 - P_(n + 1) is positive
        · norm_cast

          -- n is positive, so consider it as n + 1
          obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := by
            exists n - 1
            omega

          -- then we can seperate the two largest terms of the sum
          rw [Finset.sum_Icc_succ_top, Finset.sum_Icc_succ_top]

          -- simplify
          ring_nf

          -- then P_1 is at most n + 2
          have p_one : P 1 ≤ n + 2 := by
            have app := hP 1
            norm_num at app
            exact app.2

          -- and P_(n + 2) is also at most n + 2
          have p_n_add_one : P (n + 2) ≤ n + 2 := by
            have app := hP (n + 2)
            norm_num at app
            exact app.2

          -- Use the P_(n + 2) bound
          have lee : 6 + (∑ k ∈ Icc 1 n, k) * 2 + n * 4 - P 1 - (n + 1 + 1)
            ≤ 6 + (∑ k ∈ Icc 1 n, k) * 2 + n * 4 - P 1 - P (2 + n) := by
              refine Nat.sub_le_sub_left ?_ _
              convert p_n_add_one using 2
              ring
          refine lt_of_lt_of_le ?_ lee

          -- then the inequality is clear
          ring_nf
          omega
          -- 1 ≤ n + 1 is positive
          · omega
          -- n + 1 + 1 is positive
          · omega

    -- chain
    refine lt_of_lt_of_le ?_ le_rhs

    -- factor the denominator to cancel factor
    -- ((n + 1) * (n + 2) - 3) = n * (n + 3) - 1
    have denom_eq' : (n + 1) * (n + 2) - 3 = n * (n + 3) - 1 := by
      ring_nf
      omega

    rw [denom_eq']

    -- show "<" bound by increasing denominator by 1
    have lt : (n : ℝ) ^ 2 / ((n * (n + 3): ℕ) : ℝ)
      < ↑n ^ 2 / ((n * (n + 3) - 1 : ℕ) : ℝ) := by
        have n_pos : 0 < n := by omega
        -- to prove a / b < a / d, we just need to show that d < b
        rw [div_lt_div_iff_of_pos_left]
        -- (n * (n + 3) - 1) < (n * (n + 3))
        · norm_cast
          norm_num
          positivity
        -- n ^ 2 is positive
        · norm_cast
          positivity
        -- n * (n + 3) is positive
        · norm_cast
          positivity
        -- n * (n + 3) - 1 is positive
        · simp only [Nat.cast_pos, tsub_pos_iff_lt]
          have one_lt : 1 < n + 3 := by omega
          nlinarith

    refine lt_of_le_of_lt ?_ lt

    -- then both sides are equal
    refine le_of_eq ?_

    -- n is positive, so consider it as n + 1
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := by
      exists n - 1
      omega

    -- simplify
    field_simp
    ring

    -- we used that f' terms are positive
    · refine Fintype.sum_pos ?_
      -- there are more than 0 terms
      have fin_nonempty : Nonempty (Fin n) := by
        refine Fin.pos_iff_nonempty.mp ?_
        omega

      -- and they are all positive
      exact lt_of_strongLT f'_pos