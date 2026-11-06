import Mathlib

open Real

/- Extend 1 Let non-negative real numbers $a, b, c, x, y, z$ satisfy $a+b+c=x+y+z=1$.
Find the minimum value of $\left(a-x^{2}\right)\left(b-y^{2}\right)\left(c-z^{2}\right)$. -/
theorem inequalities_208046 :
    IsLeast {t : ℝ | ∃ a b c x y z : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧
      a + b + c = 1 ∧ x + y + z = 1 ∧ t = (a - x^2) * (b - y^2) * (c - z^2)} (-1 / 4)
  := by
    -- use ≤ instead of ≥
    simp only [ge_iff_le]

    unfold IsLeast lowerBounds

    split_ands
    -- -1 / 4 is achievable
    · simp only [Set.mem_setOf_eq]
      -- a = 0, b = c = 1 / 2, x = 1, y = z = 0
      exists 0, (1 / 2), (1 / 2), 1, 0, 0
      norm_num
    -- then we prove that -1 / 4 is a lower bound
    · simp only [Set.mem_setOf_eq]
      rintro S ⟨a, b, c, x, y, z, ah, bh, ch, xh, yh, zh, abc, xyz, rfl⟩

      -- then we have the factors f_0 = (a - x ^ 2), f_1 = (b - y ^ 2) and f_2 = (c - z ^ 2)
      let f := ![(a - x ^ 2), (b - y ^ 2), (c - z ^ 2)]

      -- then we want to prove that -1 / 4 ≤ ∏ f_i
      convert_to -1 / 4 ≤ ∏ i : Fin 3, f i
      · norm_num [Fin.prod_univ_three, f]

      -- wlog, f is monotone
      wlog hf : Monotone f generalizing f a b c x y z
      -- consider a, b, c and x, y, z as function from Fin 3 to ℝ
      -- ... abc
      · let abc : Fin 3 → ℝ := ![a, b, c]
        -- ... and xyz
        let xyz : Fin 3 → ℝ := ![x, y, z]

        -- a + b + c = 1
        have abc_sum : ∑ i : Fin 3, abc i = 1 := by
          rw [Fin.sum_univ_three]
          norm_num [abc]
          linarith

        -- x + y + z = 1
        have xyz_sum : ∑ i : Fin 3, xyz i = 1 := by
          rw [Fin.sum_univ_three]
          norm_num [xyz]
          linarith

        -- every a b and c is non-negative
        have abc_pos : ∀ i : Fin 3, 0 ≤ abc i := by
          intro i
          fin_cases i
          · norm_num [abc, ah]
          · norm_num [abc, bh]
          · norm_num [abc, ch]

        -- every x y and z is non-negative
        have xyz_pos : ∀ i : Fin 3, 0 ≤ xyz i := by
          intro i
          fin_cases i
          · norm_num [xyz, xh]
          · norm_num [xyz, yh]
          · norm_num [xyz, zh]

        -- let f' be an alternative representation of f, where each element is abc_i - xyz_i ^ 2
        let f' : Fin 3 → ℝ := fun i => abc i - (xyz i) ^ 2

        have f_eq : f = f' := by
          unfold f f'
          ext i
          unfold abc xyz
          fin_cases i
          · norm_num
          · norm_num
          · norm_num

        -- We have two representations of f' sorted by f
        have sorted_f : ![(abc ∘ ⇑(Tuple.sort f)) 0 - (xyz ∘ ⇑(Tuple.sort f)) 0 ^ 2,
          (abc ∘ ⇑(Tuple.sort f)) 1 - (xyz ∘ ⇑(Tuple.sort f)) 1 ^ 2,
          (abc ∘ ⇑(Tuple.sort f)) 2 - (xyz ∘ ⇑(Tuple.sort f)) 2 ^ 2] = f' ∘ (Tuple.sort f)
          := by
            ext i
            unfold f'
            fin_cases i
            · norm_num
            · norm_num
            · norm_num
              simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.reduceFinMk]

        -- we sort abc and xyz according to the values of f
        have app := this
          ((abc ∘ (Tuple.sort f)) 0)
          ((abc ∘ (Tuple.sort f)) 1)
          ((abc ∘ (Tuple.sort f)) 2)
          ((xyz ∘ (Tuple.sort f)) 0)
          ((xyz ∘ (Tuple.sort f)) 1)
          ((xyz ∘ (Tuple.sort f)) 2)
          (abc_pos ((Tuple.sort f) 0))
          (abc_pos ((Tuple.sort f) 1))
          (abc_pos ((Tuple.sort f) 2))
          (xyz_pos ((Tuple.sort f) 0))
          (xyz_pos ((Tuple.sort f) 1))
          (xyz_pos ((Tuple.sort f) 2))
          (by simp_rw [←Fin.sum_univ_three, Function.comp_apply, Equiv.sum_comp, abc_sum])
          (by simp_rw [←Fin.sum_univ_three, Function.comp_apply, Equiv.sum_comp, xyz_sum])

        -- simplify
        rw [sorted_f, ←f_eq] at app

        -- clearly f is monotone after sorting
        have mono : Monotone (f ∘ (Tuple.sort f)) := Tuple.monotone_sort f

        -- then we get a solution when f is not monotone
        convert app mono using 1
        · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Function.comp_apply]
          rw [Equiv.prod_comp]

      -- then we have f_0 ≤ f_1 ≤ f_2
      have f_zero_le_one : f 0 ≤ f 1 := by
        apply hf
        norm_cast

      have f_one_le_two : f 1 ≤ f 2 := by
        apply hf
        norm_cast

      -- consider when f_0 is non-negative
      by_cases f_zero : 0 ≤ f 0
      -- then f_1 and f_2 are non-negative
      · have f_one : 0 ≤ f 1 := by linarith
        have f_two : 0 ≤ f 2 := by linarith
        rw [Fin.prod_univ_three]
        -- then the product is non-negative, so the inequality holds
        trans 0
        · linarith
        · positivity

      -- so f_0 is negative
      replace f_zero : f 0 < 0 := by linarith

      -- consider when f_1 is non-negative
      by_cases f_one : 0 ≤ f 1
      -- then f_2 is non-negative too
      · have f_two : 0 ≤ f 2 := by linarith

        -- then we'll show that (x ^ 2 - a) * (b - y ^ 2) * (c - z ^ 2) ≤ 1 / 4
        rw [Fin.prod_univ_three]
        norm_num [f]
        rw [neg_le]
        convert_to (x ^ 2 - a) * (b - y ^ 2) * (c - z ^ 2) ≤ 1 / 4
        · ring

        -- clearly (x ^ 2 - a) * (b - y ^ 2) * (c - z ^ 2) ≤ x ^ 2 * b * c
        trans x ^ 2 * b * c
        -- compare each factor
        · gcongr
          · linarith
          · field_simp
          · field_simp

        -- and x ^ 2 * b * c ≤ 1 * b * c
        trans 1 * b * c
        · gcongr
          -- because x is at most 1
          have hmm : x ≤ 1 := by linarith
          exact (sq_le_one_iff₀ xh).mpr hmm

        norm_num

        -- and b * c ≤ ((b + c) / 2) ^ 2
        trans ((b + c) / 2) ^ 2
        -- according to AM-GM
        · have am_gm := @Real.geom_mean_le_arith_mean2_weighted
            (1 / 2) (1 / 2) b c (by linarith) (by linarith) bh ch (by linarith)
          field_simp at am_gm
          rw [←sq_le_sq₀] at am_gm
          convert am_gm
          rw [←Real.mul_rpow, ←Real.rpow_natCast, ←Real.rpow_mul]
          norm_num
          -- operations were valid because every term is non-negative
          all_goals positivity

        -- and ((b + c) / 2) ^ 2 ≤ (1 / 2) ^ 2
        trans (1 / 2) ^ 2
        · gcongr
          linarith

        -- finally (1 / 2) ^ 2 ≤ 1 / 4
        norm_num

      -- so f_1 is negative
      replace f_one : f 1 < 0 := by linarith

      -- consider when f_2 is non-negative
      by_cases f_two : 0 ≤ f 2
      · rw [Fin.prod_univ_three]

        -- then the product is positive
        trans 0
        · linarith

        -- product of the negative factors is positive
        have prod : 0 < f 0 * f 1 := mul_pos_of_neg_of_neg f_zero f_one
        -- so everything is non-negative
        positivity

      -- so f_2 is negative
      replace f_two : f 2 < 0 := by linarith

      -- then we'll show that (x ^ 2 - a) * (y ^ 2 - b) * (z ^ 2 - c) ≤ 1 / 4
      rw [Fin.prod_univ_three]
      norm_num
      rw [neg_le]
      norm_num [f]
      convert_to (x ^ 2 - a) * (y ^ 2 - b) * (z ^ 2 - c) ≤ 1 / 4
      · ring

      -- Call each factor g_0, g_1 and g_2.
      let g := ![(x ^ 2 - a), (y ^ 2 - b), (z ^ 2 - c)]

      -- Then each g_i is the negative of f_i
      have g_eq : g = Neg.neg ∘ f := by
        ext i
        unfold f g
        fin_cases i
        · norm_num
        · norm_num
        · norm_num

      -- each g_i is non-negative
      have g_nonneg : ∀ i ∈ Finset.univ, 0 ≤ g i := by
        norm_num
        intro i
        rw [g_eq]
        fin_cases i
        · norm_num; linarith
        · norm_num; linarith
        · norm_num
          simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue]
          linarith

      -- Use the AM-GM inequality to bound the product of g_i
      have am_gm := Real.geom_mean_le_arith_mean Finset.univ
        (fun i => (1 / 3)) g (by norm_num)
        (by norm_num)
        g_nonneg

      -- simplify
      norm_num at am_gm

      -- rewrite to isolate product on the LHS
      replace am_gm := @Real.rpow_le_rpow _ _ 3 ?_ am_gm ?_
      rw [Real.finset_prod_rpow] at am_gm
      rw [←Real.rpow_mul] at am_gm
      norm_num at am_gm
      norm_num [Fin.prod_univ_three, g] at am_gm

      -- LHS matched desired inequality
      refine am_gm.trans ?_

      rw [←Finset.mul_sum]

      -- the sum of g_i is equal to x ^ 2 + y ^ 2 + z ^ 2 - 1
      have sum_g : ∑ i : Fin 3, g i = x ^ 2 + y ^ 2 + z ^ 2 - 1 := by
        rw [Fin.sum_univ_three]
        norm_num [g]
        rw [←abc]
        ring

      rw [sum_g]

      -- but x ^ 2 + y ^ 2 + z ^ 2 is at most 1
      have sq_lee : x ^ 2 + y ^ 2 + z ^ 2 ≤ 1 := by
        -- use that 1 = x + y + z
        rw [←xyz]
        -- compare termwise
        gcongr
        · exact sq_le (by linarith) (by linarith)
        · exact sq_le (by linarith) (by linarith)
        · exact sq_le (by linarith) (by linarith)

      -- so (1 / 3 * (x ^ 2 + y ^ 2 + z ^ 2 - 1)) ^ 3 ≤ (1 / 3 * (1 - 1)) ^ 3
      trans (1 / 3 * (1 - 1)) ^ 3
      · ring_nf
        field_simp
        convert_to ((-1 + x ^ 2 + y ^ 2 + z ^ 2) / 3) ^ 3 ≤ 0
        · rw [←Real.rpow_natCast _ 3]
          norm_num

        apply Odd.pow_nonpos
        · decide
        · linarith

      -- then the inequality clearly holds
      norm_num

      -- Operations were valid because every value is positive
      · exact Finset.prod_nonneg g_nonneg
      · exact g_nonneg
      · apply Finset.prod_nonneg
        intro i ih
        apply Real.rpow_nonneg
        exact g_nonneg i ih
      · linarith