import Mathlib

/- For $t = 1, 2, 3, 4$, define $S_t = \sum_{i = 1}^{350}a_i^t$, where $a_i \in \{1,2,3,4\}$. If $S_1 = 513$ and $S_4 = 4745$, find the minimum possible value for $S_2$. -/
theorem algebra_94108 :
  IsLeast ((fun a => ∑ i ∈ Finset.range 350, (a i) ^ 2) '' {a : ℕ → ℕ | (∀ i, a i ∈ Finset.Icc 1 4) ∧ ∑ i ∈ Finset.range 350, a i = 513 ∧ ∑ i ∈ Finset.range 350, (a i) ^ 4 = 4745}) 905
  := by
    -- We can rewrite allowed `a` as four variables, `w x y z`, counting the number of 1s, 2s, etc, with linear equations as restrictions
    have as_nat : (fun a => ∑ i ∈ Finset.range 350, (a i) ^ 2) '' {a : ℕ → ℕ | (∀ i, a i ∈ Finset.Icc 1 4) ∧ ∑ i ∈ Finset.range 350, a i = 513 ∧ ∑ i ∈ Finset.range 350, (a i) ^ 4 = 4745}
      = (fun ⟨w, x, y, z⟩ => w + x * 4 + y * 9 + z * 16)
        '' {⟨w, x, y, z⟩ : ℕ × ℕ × ℕ × ℕ | w + x + y + z = 350 ∧ w + x * 16 + y * 81 + z * 256 = 4745 ∧ w + x * 2 + y * 3 + z * 4 = 513}
      := by
        ext xo
        simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists]
        constructor
        -- Given `a`, `w x y z` has the required properties
        · intro ⟨a, ⟨ha, h1, h4⟩, tmp⟩
          let w := ((Finset.range 350).filter (a · = 1)).card
          let x := ((Finset.range 350).filter (a · = 2)).card
          let y := ((Finset.range 350).filter (a · = 3)).card
          let z := ((Finset.range 350).filter (a · = 4)).card
          refine ⟨w, x, y, z, ?_⟩
          rw [←tmp]
          clear tmp xo
          refine ?_

          -- Filtering elements which `a` map to different values creates disjoint sets
          have dis : ∀ {k1 k2}, k1 ≠ k2 → Disjoint
            ((Finset.range 350).filter (a · = k1))
            ((Finset.range 350).filter (a · = k2))
            := by
              intro k1 k2 ne
              rw [Finset.disjoint_filter]
              intro aa bb cc
              exact cc ▸ ne

          -- Summing over values which `a` map to some value `k` can be
          -- written `x * f k` where x is the number of values which map to `k`.
          have sum_eq : ∀ (k : ℕ) (f: ℕ → ℕ), ∑ x ∈ (Finset.range 350).filter (a · = k), f (a x)
            = ((Finset.range 350).filter (a · = k)).card * f k
            := by
              intro k f
              apply Finset.sum_eq_card_nsmul
              intro xx
              simp only [Finset.mem_filter, and_imp]
              intro aa bb
              rw [bb]

          -- We can split up the range into the possible values of `a`.
          have parts : Finset.range 350
            = (Finset.range 350).filter (a · = 1)
            ∪ (Finset.range 350).filter (a · = 2)
            ∪ (Finset.range 350).filter (a · = 3)
            ∪ (Finset.range 350).filter (a · = 4) := by
            ext x
            simp
            by_cases hh : x < 350
            · simp only [hh, true_and, true_iff]
              have hue := ha x
              obtain ⟨l, u⟩ := Finset.mem_Icc.mp hue
              set hm := a x
              interval_cases hm <;> decide
            · simp only [hh, false_and, or_self]


          -- we can convert sums into linear combinations
          have as_linear : ∀ f : ℕ → ℕ, ∑ i ∈ Finset.range 350, f (a i) = w * (f 1) + x * (f 2) + y * (f 3) + z * (f 4) := by
            intro f
            rw [parts, Finset.sum_union, Finset.sum_union, Finset.sum_union,
              sum_eq, sum_eq, sum_eq, sum_eq]
            rw [Finset.disjoint_filter]
            intro aa bb cc
            rw [cc]
            decide
            simp only [Finset.disjoint_union_left]
            refine ⟨?_, ?_⟩
            · exact dis (by decide)
            · exact dis (by decide)
            simp only [Finset.union_assoc, Finset.disjoint_union_left]
            exact ⟨dis (by decide), dis (by decide), dis (by decide)⟩

          -- Now we can convert our hypotheses and the minimizing function to linear combinations of `w x y z`
          refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
          -- We have w + x + y + z = 350, because the range of values is 350
          · have yeah1 : (Finset.range 350).card = 350 := Finset.card_range 350
            rw [←yeah1, Finset.card_eq_sum_ones]
            have yeah2 : ∑ x ∈ Finset.range 350, 1 = ∑ x ∈ Finset.range 350, Function.const ℕ 1 (a x) := by
              simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, Function.const_apply]
            rw [yeah2, as_linear]
            simp only [Function.const_apply, mul_one]
          -- we have w + x * 16 + y * 81 + z * 256 = 4745
          · rw [as_linear (fun x => x ^ 4)] at h4
            simp only [one_pow, mul_one, Nat.reducePow] at h4
            exact h4
          -- we have w + x * 2 + y * 3 + z * 4 = 513
          · replace h1 : ∑ i ∈ Finset.range 350, id (a i) = 513 := by
              simp only [id_eq]
              exact h1
            rw [as_linear id] at h1
            simp only [id_eq, mul_one] at h1
            exact h1
          -- our minimizing function is equal to w + x * 4 + y * 9 + z * 16
          · rw [as_linear (fun x => x ^ 2)]
            simp only [one_pow, mul_one, Nat.reducePow, and_true]

        -- Given `w x y z`, we will construct `a` so that `w` counts 1s, `x` counts 2s, etc.
        · intro ⟨w, x, y, z, ⟨r1, r3⟩, r2⟩
          let a : ℕ → ℕ := by
            intro nn
            by_cases h1 : nn < w
            · exact 1
            by_cases h2 : nn < w + x
            · exact 2
            by_cases h2 : nn < w + x + y
            · exact 3
            · exact 4

          -- Sums over `a` can be written as a linear combination of `w x y z`
          have sum_eq : ∀ g : ℕ → ℕ, ∑ i ∈ Finset.range 350, g (a i)
            = w * g 1 + x * g 2 + y * g 3 + z * g 4 := by
              intro g
              have le_z : w + x + y ≤ 350 := by linarith
              have le_y : w + x ≤ w + x + y := by linarith
              have le_x : w ≤ w + x := by linarith

              -- We split the sum up into its four parts
              rw [
                ←Finset.sum_range_add_sum_Ico _ le_z,
                ←Finset.sum_range_add_sum_Ico _ le_y,
                ←Finset.sum_range_add_sum_Ico _ le_x
              ]

              -- Each sum is over a constant value
              convert_to ∑ k ∈ Finset.range w, g 1
                + ∑ k ∈ Finset.Ico w (w + x), g 2
                + ∑ k ∈ Finset.Ico (w + x) (w + x + y), g 3
                + ∑ k ∈ Finset.Ico (w + x + y) 350, g 4
                = w * g 1 + x * g 2 + y * g 3 + z * g 4
              congr 1
              congr 1
              congr 1
              -- First sum is over 1s
              · apply Finset.sum_congr rfl
                intro i b
                simp only [Finset.mem_range] at b
                simp only [a, b, ↓reduceDIte]
              -- Second sum is over 2s
              · apply Finset.sum_congr rfl
                intro i b
                simp only [Finset.mem_Ico] at b
                have nlt : ¬i < w := by
                  simp only [not_lt]
                  exact b.1
                simp only [a, nlt, ↓reduceDIte, b.2]
              -- Third sum is over 3s
              · apply Finset.sum_congr rfl
                intro i b
                congr
                simp only [Finset.mem_Ico] at b
                have nlt : ¬i < w := not_lt.mpr <| le_x.trans b.1
                have nlt2 : ¬i < w + x := not_lt.mpr b.1
                simp only [dite_eq_ite, nlt, ↓reduceIte, nlt2, ite_eq_left_iff, not_lt,
                  Nat.succ_ne_self, imp_false, not_le, gt_iff_lt, a]
                exact b.2
              -- Fourth sum is over 4s
              · apply Finset.sum_congr rfl
                intro i b
                congr
                simp only [Finset.mem_Ico] at b
                have yep : ¬i < w := by
                  refine not_lt.mpr ?_
                  refine le_trans ?_ b.1
                  exact Nat.le_add_right_of_le le_x
                have yep2 : ¬i < w + x := not_lt.mpr <| le_y.trans b.1
                simp only [dite_eq_ite, yep, ↓reduceIte, yep2, ite_eq_right_iff, Nat.reduceEqDiff,
                  imp_false, not_lt, ge_iff_le, a]
                exact b.1

              -- But sums over constants can be simplified, and we're done
              simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, Nat.card_Ico,
                add_tsub_cancel_left]
              rw [←r1]
              simp only [add_tsub_cancel_left]
          -- We use our `a` and show that it has the required properties
          refine ⟨a, ?_⟩
          refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
          -- it's always in [1, 4]
          · intro i
            rw [Finset.mem_Icc]
            refine ⟨?_, ?_⟩
            simp only [dite_eq_ite, a]
            split_ifs with hh <;> decide
            simp only [dite_eq_ite, a]
            split_ifs with hh <;> decide
          -- We express the sums as linear combinations
          · have with_id : ∑ i ∈ Finset.range 350, a i = ∑ i ∈ Finset.range 350, id (a i) := by
              congr
            rw [with_id, sum_eq id]
            simp only [id_eq, mul_one]
            exact r3.2
          · rw [sum_eq (fun x => x ^ 4)]
            simp only [one_pow, mul_one, Nat.reducePow]
            exact r3.1
          · rw [sum_eq (fun x => x ^ 2)]
            simp only [one_pow, mul_one, Nat.reducePow]
            exact r2
    rw [as_nat]
    simp only [IsLeast, Set.mem_image, Set.mem_setOf_eq, Prod.exists]

    -- We start by showing that 905 is a lower bound
    refine ⟨?_, ?_⟩
    rotate_left
    · rw [mem_lowerBounds]
      simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists, forall_exists_index, and_imp]
      intro tmp w x y z h0 h4 h1 h2
      rw [←h2]
      clear h2 tmp as_nat

      -- We have an expression for w
      have w_eq : (w : ℤ) = 350 - x - y - z := by linarith

      -- We substitute it into our other equations to just consider three variables
      have eq_163 : x + 2 * y + 3 * z = 163 := by linarith
      have eq_4395 : 15 * x + 80 * y + 255 * z = 4395 := by linarith

      -- we reduce the second equation
      have eq_879 : 3 * x + 16 * y + 51 * z = 879 := by linarith

      -- we then have an expression for x
      have x_eq : (x : ℤ) = 163 - 2 * y - 3 * z := by linarith

      -- then we can just consider two variables
      have eq_195 : 5 * y + 21 * z = 195 := by linarith

      -- then we get an upper bound for z
      have : 21 * z ≤ 195 := by linarith
      have : z ≤ 10 := by linarith
      -- we consider the possible values of z and find that z = 0 and z = 5 works,
      -- and both are above the minimum
      interval_cases z <;> omega
    -- Taking inspiration from when we proved the lower bound,
    -- we see that w = 215, x = 112, y = 18, z = 5 achieves the minimum 905
    · refine ⟨215, 112, 18, 5, ?_⟩
      decide