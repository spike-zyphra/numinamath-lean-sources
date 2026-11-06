import Mathlib

/- AM-GM inequality variant for a finite number of real non-negative variables. -/
lemma Fin_geom_mean_le_arith_mean {n : ℕ} [NeZero n]
  {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i)
  : n * (∏ j, a j) ^ (1 / n : ℝ) ≤ ∑ j, a j := by

    -- apply AM-GM to a, where equal weights of (1 / n)
    have am_gm := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1 / n : ℝ)) a
      (fun _ _ => Nat.one_div_cast_nonneg n) (by norm_num) (fun i a => ha i)

    -- the weights sum to 1
    have weights_sum_one : (∑ i : Fin n, (fun x => (1 / n : ℝ)) i) = 1 := by norm_num

    -- simplify AM-GM
    norm_num [weights_sum_one, ←Finset.mul_sum] at am_gm

    -- n is positive
    have n_pos : (0 : ℝ) < n := by norm_num [Nat.pos_of_neZero n]

    -- multiply both sides by n
    replace am_gm := (mul_le_mul_left n_pos).mpr am_gm

    -- we have the desired inequality
    convert am_gm
    -- lhs is equal
    -- power distributes over product
    · rw [Real.finset_prod_rpow]
      norm_num
      · norm_num [ha]
    -- rhs is equal
    · field_simp

/- Given a sequence of n non-negative real numbers, their product
  is upper bounded by their sum divided by n to the power of n. -/
lemma Fin_prod_le {n : ℕ} [NeZero n]
  {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i)
  : ∏ j, a j ≤ ((∑ j, a j) / n) ^ n := by
    -- use AM-GM
    have am_gm := Fin_geom_mean_le_arith_mean ha
    -- the product is positive
    have prod_pos : 0 ≤ ∏ j : Fin n, a j
      := Finset.prod_nonneg fun i a => ha i

    -- divide both sides by n
    rw [mul_comm, ←le_div_iff₀] at am_gm
    -- n is non-negative
    have n_nonneg : (0 : ℝ) ≤ n := by linarith

    -- square both sides of AM-GM by n
    convert Real.rpow_le_rpow ?_ am_gm n_nonneg
    · norm_num [←Real.rpow_mul prod_pos]
    · norm_num
    · positivity
    · norm_cast
      exact Nat.pos_of_neZero n

/- Example 3 Let $a_{1}, a_{2}, \cdots, a_{n}$ be non-negative real numbers, and satisfy $\sum_{i=1}^{n} a_{i}=4(n \geqslant 3)$. Try to prove: $a_{1}^{3} a_{2}+a_{2}^{3} a_{3}+\cdots+a_{n-1}^{3} a_{n}+a_{n}^{3} a_{1} \leqslant 27$. -/
theorem inequalities_114184 {n : ℕ} (hn : 3 ≤ n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 4) :
    ∑ i : Fin n, (a i)^3 * a (finRotate n i) ≤ 27
  := by

    -- n is not zero
    have : NeZero n := NeZero.of_gt hn

    -- Rotating Fin n by 1 is the same as adding 1 (mod n)
    convert_to ∑ i : Fin n, (a i) ^ 3 * a (i + 1) ≤ 27
    · obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1
        := Nat.exists_eq_succ_of_ne_zero (by omega)
      norm_num

    -- we prove by induction on n, starting at n = 3
    induction' n, hn using Nat.le_induction with n1 h1 h2
    -- wlog, a_0 is the largest element
    · wlog hs : a 0 = ⨆ i : Fin 3, a i generalizing a
      -- if a_0 is not the largest, then there's some other a_b which is largest
      · obtain ⟨b, bh⟩ : ∃ i, a i = ⨆ i : Fin 3, a i := exists_eq_ciSup_of_finite
        -- so we rotate a values so that a_b is first
        let off : Equiv.Perm (Fin 3) := {
          toFun := (b + ·)
          invFun := (· - b)
          left_inv := add_sub_cancel_left b
          right_inv := add_sub_cancel b
        }
        -- then we can consider the rotated sequence
        let a' := a ∘ off

        -- it's positive
        have pos : ∀ (i : Fin 3), 0 ≤ a' i := (ha <| off ·)

        -- it sums to 4
        have sum : ∑ i : Fin 3, a' i = 4 := by
          simpa only [a', Function.comp_apply, Equiv.sum_comp] using hsum

        -- a'_0 is the largest element
        have eq_sup : a' 0 = ⨆ i, a' i := by
          norm_num [a', Equiv.iSup_comp off, ←bh]
          norm_num [off]

        convert this a' pos sum eq_sup using 1
        -- ∑ a i ^ 3 * a (i + 1) = ∑ a' i ^ 3 * a' (i + 1)
        -- because a' is just a permutation
        · norm_num [a']
          rw [←Equiv.sum_comp off]
          congr
          norm_num [off]
          ext i
          ring_nf

      -- so then a_1 ≤ a_0
      have a_1_le : a 1 ≤ a 0 := by
        rw [hs]
        exact le_ciSup (Finite.bddAbove_range a) 1

      -- and a_2 ≤ a_0
      have a_2_le : a 2 ≤ a 0 := by
        rw [hs]
        exact le_ciSup (Finite.bddAbove_range a) 2

      -- we know that the values 0, 1 and 2 are if we swap 1 and 2
      have swap_eq_0 : ((Equiv.swap 1 2) 0) = (0 : Fin 3)
        := by norm_num [Equiv.swap_apply_def]; omega
      have swap_eq_1 : ((Equiv.swap 1 2) 1) = (2 : Fin 3)
        := by norm_num [Equiv.swap_apply_def]
      have swap_eq_2 : ((Equiv.swap 1 2) 2) = (1 : Fin 3)
        := by norm_num [Equiv.swap_apply_def]

      -- and we know that 3 is 0, if we consider values modulo 3
      have fin_three : (3 : Fin 3) = 0 := by rfl

      -- wlog, we have a_2 ≤ a_1
      wlog len : a 2 ≤ a 1 generalizing a
      -- if not, we just swap 1 and 2
      · have app := this (a ∘ (Equiv.swap 1 2))
        norm_num [swap_eq_0, swap_eq_1, swap_eq_2] at app

        -- they are still all positive
        replace app := app (ha <| Equiv.swap 1 2 <| ·)

        -- they still sum to 4
        have sum_eq : ∑ x : Fin 3, a ((Equiv.swap 1 2) x) = 4 := by
          rw [Equiv.sum_comp]
          tauto

        replace app := app sum_eq

        -- a_0 is still the largest element
        have sup_eq : a 0 = ⨆ i, a ((Equiv.swap 1 2) i) := by
          rw [Equiv.iSup_comp (Equiv.swap 1 2), hs]

        -- so we have
        -- ∑ x, a ("swap 1 and 2" x) ^ 3 * a ("swap 1 and 2" (x + 1)) ≤ 27
        replace app := app sup_eq (by tauto) (by tauto) (by linarith)

        -- but by swapping 1 and 2, we increased the sum
        refine le_trans ?_ app

        -- simplify
        rw [←sub_nonpos, Fin.sum_univ_three, Fin.sum_univ_three]
        ring_nf
        rw [fin_three, swap_eq_0, swap_eq_1, swap_eq_2]
        ring_nf

        -- group into factors
        convert_to (a 0 - a 1) * (a 1 - a 2) * (a 0 - a 2) * (a 0 + a 1 + a 2) ≤ 0
        · ring_nf

        -- three factors are non-negative and one is non-positive
        have pos_1 : 0 ≤ (a 0 - a 1) := by linarith
        have pos_2 : (a 1 - a 2) ≤ 0 := by linarith
        have pos_3 : 0 ≤ (a 0 - a 2) := by linarith
        have pos_4 : 0 ≤ (a 0 + a 1 + a 2) := by
          have a_0_pos := ha 0
          have a_1_pos := ha 1
          have a_2_pos := ha 2
          positivity

        -- so their product is non-positive
        have part_1 : (a 0 - a 1) * (a 1 - a 2) ≤ 0
          := mul_nonpos_of_nonneg_of_nonpos pos_1 pos_2
        have part_2 : (a 0 - a 1) * (a 1 - a 2) * (a 0 - a 2) ≤ 0
          := mul_nonpos_of_nonpos_of_nonneg part_1 pos_3
        exact mul_nonpos_of_nonpos_of_nonneg part_2 pos_4

      -- so we have that a_2 ≤ a_1

      -- note that a_0, a_1 and a_2 are all non-negative
      have a_0_pos := ha 0
      have a_1_pos := ha 1
      have a_2_pos := ha 2


      -- expand sum and simplify
      rw [Fin.sum_univ_three]
      norm_num
      rw [fin_three]

      -- then we just need to show that
      -- a_0 ^ 3 * a_1 + a_1 ^ 3 * a_2 + a_2 ^ 3 * a_0 ≤ 27
      calc a 0 ^ 3 * a 1 + a 1 ^ 3 * a 2 + a 2 ^ 3 * a 0
        -- reorganize
        _ = a 0 ^ 3 * a 1 + ((a 2) * (a 1 ^ 2 * (a 1) + a 2 * a 2 * a 0)) := by ring
        -- use bound on a_i
        _ ≤ a 0 ^ 3 * a 1 + (a 2) * ((a 0) ^ 2 * a 1 + a 0 * a 1 * a 0) := by gcongr
        -- re-organize
        _ = a 0 ^ 3 * a 1 + 2 * (a 0) ^ 2 * (a 1) * (a 2) := by ring
        -- increase a factor 2 → 3
        _ ≤ a 0 ^ 3 * a 1 + 3 * (a 0) ^ 2 * (a 1) * (a 2) := by gcongr; linarith
        -- factor out 1 / 3
        _ = (1 / 3) * (a 0 * a 0 * 3 * a 1 * (a 0 + 3 * a 2)) := by ring
        -- use AM-GM for upper bound on product of terms
        _ ≤ (1 / 3) * ((a 0 + a 0 + 3 * a 1 + (a 0 + 3 * a 2)) / 4) ^ 4 := by
          gcongr 1 / 3 * ?_
          let f := ![a 0, a 0, 3 * a 1, (a 0 + 3 * a 2)]
          have pos : ∀ i, 0 ≤ f i := by
            intro i
            unfold f
            fin_cases i <;> (norm_num; positivity)
          have bound := Fin_prod_le pos
          norm_num [Fin.prod_univ_four, f, Fin.sum_univ_four] at bound
          ring_nf at bound ⊢
          exact bound
        -- simplify
        _ = (1 / 3) * ((3 * (a 0 + a 1 + a 2)) / 4) ^ 4 := by ring
        -- use a_0 + a_1 + a_2 = 4, then calculate
        _ = (27 : ℝ) := by
          norm_num [Fin.sum_univ_three] at hsum
          rw [hsum]
          ring
    -- for the induction case, we prove that wlog, a_0 is the largest element
    -- proving it separately in the base case and induction case allows us to apply the induction hypothesis
    -- on sequences where the first element may not be the largest.
    · wlog hs : a 0 = ⨆ i : Fin (n1 + 1), a i generalizing a
      -- if a_0 is not the largest, then there's some other a_b which is largest
      · obtain ⟨b, bh⟩ : ∃ i, a i = ⨆ i : Fin (n1 + 1), a i := exists_eq_ciSup_of_finite
        -- so we rotate a values so that a_b is first
        let off : Equiv.Perm (Fin (n1 + 1)) := {
          toFun := (b + ·)
          invFun := (· - b)
          left_inv := add_sub_cancel_left b
          right_inv := add_sub_cancel b
        }
        -- then we can consider the rotated sequence
        let a' := a ∘ off

        -- it's positive
        have pos : ∀ (i : Fin (n1 + 1)), 0 ≤ a' i := (ha <| off ·)

        -- it sums to 4
        have sum : ∑ i : Fin (n1 + 1), a' i = 4 := by
          simpa only [a', Function.comp_apply, Equiv.sum_comp] using hsum

        -- a'_0 is the largest element
        have eq_sup : a' 0 = ⨆ i, a' i := by
          norm_num [a', Equiv.iSup_comp off, ←bh]
          norm_num [off]

        convert this a' pos sum eq_sup using 1
        -- ∑ a i ^ 3 * a (i + 1) = ∑ a' i ^ 3 * a' (i + 1)
        -- because a' is just a permutation
        · norm_num [a']
          rw [←Equiv.sum_comp off]
          congr
          norm_num [off]
          ext i
          ring_nf

      -- we have that n1 is at least 3, so consider it as n1 + 3
      obtain ⟨n1, rfl⟩ : ∃ n', n1 = n' + 3
        := Nat.exists_eq_add_of_le' h1

      -- let a' be the sequence where we've added together a_1 and a_2
      let a' : Fin (n1 + 3) → ℝ := Fin.cons (a 0) <| Fin.cons (a 1 + a 2) <| Fin.tail <| Fin.tail <| Fin.tail a

      -- then a'_0 = a_0
      have a'_0 : a' 0 = a 0 := by norm_num [a']
      -- then a'_1 = a_1 + a_2
      have a'_1 : a' 1 = a 1 + a 2 := by norm_num [a']
      -- then a'_2 = a_3
      have a'_2 : a' 2 = a 3 := by
        norm_num [a']
        have eq_2 : (2 : Fin (n1 + 3)) = (0 : Fin (n1 + 1)).succ.succ := by norm_num
        rw [eq_2, Fin.cons_succ, Fin.cons_succ]
        norm_num [Fin.tail]
        congr

      -- then we have that
      -- ∑ x, a x ^ 3 * a (x + 1) ≤ ∑ x, a' x ^ 3 * a' (x + 1)
      trans ∑ x : Fin (n1 + 3), a' x ^ 3 * a' (x + 1)
      -- extract the first three terms from the a sum
      · iterate 3 rw [Fin.sum_univ_succ]
        -- and two terms from the a' sum
        rw [Fin.sum_univ_succ (fun x => a' x ^ 3 * a' (x + 1))]
        rw [Fin.sum_univ_succ (fun i => a' i.succ ^ 3 * a' (i.succ + 1))]

        -- the remaining sums are equal
        have sum_eq : ∑ i : Fin (n1 + 1), a i.succ.succ.succ ^ 3 * a (i.succ.succ.succ + 1)
          = ∑ i : Fin (n1 + 1), a' i.succ.succ ^ 3 * a' (i.succ.succ + 1) := by
          congr
          ext i
          unfold a'
          norm_num

          -- we consider the last term separately
          induction' i using Fin.lastCases with h3 h4
          · norm_num
            refine Or.inl ?_
            congr
          · congr
            -- use just "succ"
            have eq_succ : h3.castSucc.succ.succ + 1 = h3.succ.succ.succ := by
              ext
              cases' h3 with x xh
              norm_num [Fin.val_add_one_of_lt, Fin.last, xh]
            have eq_succ' : h3.castSucc.succ.succ.succ + 1 = h3.succ.succ.succ.succ := by
              ext
              cases' h3 with x xh
              norm_num [Fin.val_add_one_of_lt, Fin.last, xh]
            norm_num [eq_succ, eq_succ', Fin.tail]

        rw [sum_eq]
        -- let S be the sum
        set S := ∑ i : Fin (n1 + 1), a' i.succ.succ ^ 3 * a' (i.succ.succ + 1)

        -- simplify
        norm_num

        -- consider just a values
        rw [a'_0, a'_1, a'_2]

        -- normalize
        ring_nf

        -- all a values are positive
        have a_0_pos := ha 0
        have a_1_pos := ha 1
        have a_2_pos := ha 2
        have a_3_pos := ha 3

        -- simplify
        field_simp

        -- group values to make the inequality more clear
        convert_to a 0 ^ 3 * a 1 + a 1 ^ 3 * a 2 + 0 ≤ a 0 ^ 3 * a 1 + a 0 ^ 3 * a 2 + (a 1 * a 2 ^ 2 * a 3 * 3 + a 1 ^ 2 * a 2 * a 3 * 3 + a 1 ^ 3 * a 3)
        · ring
        · ring

        -- remember that a_1 ≤ a_0
        have a_1_le : a 1 ≤ a 0 := by
          rw [hs]
          exact le_ciSup (Finite.bddAbove_range a) 1
        -- and a_2 ≤ a_0
        have a_2_le : a 2 ≤ a 0 := by
          rw [hs]
          exact le_ciSup (Finite.bddAbove_range a) 2

        -- consider inequality term-wise, it's all positive
        gcongr; positivity

      -- then we just need to show that
      -- ∑ x, a' x ^ 3 * a' (x + 1) ≤ 27
      -- we use the induction hypothesis
      apply h2
      -- every term is positive
      · intro i
        cases' i using Fin.cases with i
        · rw [a'_0]
          exact ha 0

        cases' i using Fin.cases with i
        · norm_num [a'_1]
          have a_1_pos := ha 1
          have a_2_pos := ha 2
          positivity

        norm_num [a', Fin.tail]
        exact ha i.succ.succ.succ
      -- the sequence sums to 4
      -- seperate first two terms from sum
      · iterate 2 rw [Fin.sum_univ_succ]
        -- consider everything as a values
        norm_num [a'_0, a'_1, a', Fin.tail]

        -- merge everything into the same sum
        let f0 := (fun i : Fin (n1 + 1 + 1) => a i.succ.succ)
        let f1 := (fun i : Fin (n1 + 1 + 1 + 1) => a i.succ)
        convert_to a 0 + (f1 0 + (f0 0 + ∑ x : Fin (n1 + 1), a x.succ.succ.succ)) = 4
        · norm_num [f0, f1]
          ring
        rw [←Fin.sum_univ_succ]
        norm_num [f0, ←Fin.sum_univ_succ]
        norm_num [f1, ←Fin.sum_univ_succ]

        -- then it's just the sum over a values, which we already know is 4
        tauto