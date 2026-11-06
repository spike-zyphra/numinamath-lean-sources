import Mathlib

open Polynomial

/- Two ants start at the same point in the plane. Each minute they choose whether to walk due north, east, south or west. They each walk 1 meter in the first minute. In each subsequent minute the distance they walk is multiplied by a rational number $q>0$. They meet after a whole number of minutes, but have not taken exactly the same route within that time. Determine all possible values of $q$.
(United Kingdom) -/
theorem combinatorics_605579 (q : ℚ) (hq : q > 0) :
    (∃ (n : ℕ) (r1 r2 : Fin (n + 1) → ℚ × ℚ),
      r1 ≠ r2
      ∧ (r1 0 = r2 0)
      ∧ (∀ i : Fin n,
        r1 i.succ = (r1 i.castSucc) + (q ^ i.val, 0)
      ∨ r1 i.succ = (r1 i.castSucc) - (q ^ i.val, 0)
      ∨ r1 i.succ = (r1 i.castSucc) + (0, q ^ i.val)
      ∨ r1 i.succ = (r1 i.castSucc) - (0, q ^ i.val))
      ∧ (∀ i : Fin n,
        r2 i.succ = (r2 i.castSucc) + (q ^ i.val, 0)
      ∨ r2 i.succ = (r2 i.castSucc) - (q ^ i.val, 0)
      ∨ r2 i.succ = (r2 i.castSucc) + (0, q ^ i.val)
      ∨ r2 i.succ = (r2 i.castSucc) - (0, q ^ i.val)) ∧
      (r1 (Fin.last n) = r2 (Fin.last n))) ↔ q = 1
  := by

    -- We can reduce telescoping sums of rationals
    have sum_fin_sub {n : ℕ} (f : Fin (n + 1) → ℚ)
      : ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
        induction' n with h1 h2
        · norm_num
        · rw [Fin.sum_univ_succ]
          have h22 := h2 (Fin.tail f)
          simp only [Fin.tail, Fin.succ_castSucc] at h22
          rw [h22]
          norm_num

    -- we call a 2D path of length n "cardinal_{o, q}" if it moves north, west, south, east at
    -- each time step, moving a distance of q ^ 0 on the first step and then
    -- multiplying the next distance moved by q each step.
    let cardinal (o : ℕ) (q : ℚ) {n : ℕ} (f : Fin (n + 1) → ℚ × ℚ) : Prop :=
      ( ∀ i : Fin n,
          f i.succ = (f i.castSucc) + (q ^ (i.val + o), 0)
        ∨ f i.succ = (f i.castSucc) - (q ^ (i.val + o), 0)
        ∨ f i.succ = (f i.castSucc) + (0, q ^ (i.val + o))
        ∨ f i.succ = (f i.castSucc) - (0, q ^ (i.val + o)))

    -- we show that q can't be 2, for any paths. We'll reuse this
    -- later to show that q can't be 1 / 2 either, because then q = 2 would work too.
    have q_half (q : ℚ) (hq : q > 0) (n : ℕ) (r1 r2 : Fin (n + 1) → ℚ × ℚ) (nee : r1 ≠ r2) (first_eq : r1 0 = r2 0)
      (h1 : cardinal 0 q r1)
      (h2 : cardinal 0 q r2)
      (last_eq : r1 (Fin.last n) = r2 (Fin.last n)) : q ≠ (1 / 2) := by

        -- we consider the subpaths r'_1 and r'_2 where their first coordinates
        -- are equal, their second are non-equal and the final one is equal again.
        obtain ⟨o, k, r1', r2', h6, h7, h8, h9, h10⟩
          : ∃ (o k : ℕ) (r1' r2' : Fin (k + 2) → ℚ × ℚ),
            cardinal o q r1'
          ∧ cardinal o q r2'
          ∧ r1' 1 ≠ r2' 1
          ∧ r1' 0 = r2' 0
          ∧ r1' (Fin.last (k + 1)) = r2' (Fin.last (k + 1))
            := by
              -- there's at least some timestep "o" where their coordinates are equal and then unequal at "o" + 1.
              obtain ⟨o, zero_eq, one_ne⟩ : ∃ i : Fin n, r1 i.castSucc = r2 i.castSucc ∧ r1 i.succ ≠ r2 i.succ := by
                -- else assume opposite
                by_contra hh
                simp only [ne_eq, not_exists, not_and, not_not] at hh

                -- then they are both equal
                have r1_eq_r2 : r1 = r2 := funext_iff.mpr <| Fin.induction first_eq hh

                -- but r_1 ≠ r_2
                contradiction

              -- Our new paths will start at o, and have a length of n - o - 1
              exists o.val, n - o.val - 1

              -- the paths are just r_1 and r_2 after skipping o timesteps
              exists fun i => r1 ⟨i.val + o.val, by omega⟩
              exists fun i => r2 ⟨i.val + o.val, by omega⟩
              norm_num
              have eqq : (o + (n - o - 1 + 1) : ℕ) = n := by omega
              split_ands
              · simp only [Fin.val_succ, Fin.coe_castSucc, cardinal]
                intro i
                specialize h1 (Fin.cast eqq (Fin.natAdd o i))
                simp only [Fin.coe_cast, Fin.coe_natAdd, add_comm o.val, add_zero] at h1
                convert h1
                all_goals
                · simp only [Fin.val_succ, Fin.coe_cast, Fin.coe_natAdd, Fin.coe_castSucc]
                  omega
              · simp only [Fin.val_succ, Fin.coe_castSucc, cardinal]
                intro i
                specialize h2 (Fin.cast eqq (Fin.natAdd o i))
                simp only [Fin.coe_cast, Fin.coe_natAdd, add_comm o.val, add_zero] at h2
                convert h2
                all_goals
                · simp only [Fin.val_succ, Fin.coe_cast, Fin.coe_natAdd, Fin.coe_castSucc]
                  omega
              · convert one_ne <;> (simp only [Fin.val_succ]; omega)
              · exact zero_eq
              · convert last_eq using 2 <;> (ext; simp only [Fin.val_last]; omega)

        -- as q us positive |q| = q
        have abs_eq : |q| = q := by
          simp only [abs_eq_self]
          positivity

        -- if we have some path r which is cardinal_{o, q}, then r(i + 1) = r(i) + p
        -- where p is (q ^ (i.val + o), 0)
        -- or -(q ^ (i.val + o), 0)
        -- or  (0, q ^ (i.val + o))
        -- or -(0, q ^ (i.val + o))
        have add_cases (i : Fin (k + 1)) (r : Fin (k + 2) → ℚ × ℚ) (hr : cardinal o q r)
          : ∃ p, r i.succ = r i.castSucc + p
            ∧ ( p = (q ^ (i.val + o), 0)
              ∨ p = -(q ^ (i.val + o), 0)
              ∨ p = (0, q ^ (i.val + o))
              ∨ p = -(0, q ^ (i.val + o)))
          := by
            specialize hr i
            norm_num at hr
            rcases hr with hh | hh | hh | hh
            · exists (q ^ (i.val + o), 0)
              tauto
            · rw [sub_eq_add_neg] at hh
              exists -(q ^ (i.val + o), 0)
              tauto
            · exists (0, q ^ (i.val + o))
              tauto
            · rw [sub_eq_add_neg] at hh
              exists -(0, q ^ (i.val + o))
              tauto
        -- we have |r'_2_x(1) - r'_1_x(1)| + |r'_2_y(1) - r'_1_y(1)| = 2 * q ^ o
        have abs_1 : |(r2' 1).1 - (r1' 1).1|
          + |(r2' 1).2 - (r1' 1).2| = 2 * q ^ o := by

          -- let k1 and k2 be the first steps
          obtain ⟨k1, h1, k1_cases⟩ := add_cases 0 r1' h6
          obtain ⟨k2, h2, k2_cases⟩ := add_cases 0 r2' h7
          norm_num at h1 h2
          norm_num [h1, h2, h9]

          -- they did not walk in the same direction
          have k1_ne_k2 : k1 ≠ k2 := by
            by_contra eqq
            rw [h1, h2, h9, eqq] at h8
            contradiction

          -- they walk positive lengths
          have pos : 0 ≤ q ^ o := by positivity

          -- consider every possible direction
          rcases k1_cases with rfl | rfl | rfl | rfl
          · rcases k2_cases with rfl | rfl | rfl | rfl
            · exact (k1_ne_k2 rfl).elim
            · simp only [Fin.val_zero, zero_add, Prod.neg_mk, neg_zero, sub_self, abs_zero, add_zero]
              ring_nf
              simp only [abs_neg, abs_eq_self, Nat.ofNat_pos, mul_nonneg_iff_of_pos_right, pos]
            · norm_num [abs_eq]
              exact (two_mul (q ^ o)).symm
            · norm_num [abs_eq]
              exact (two_mul (q ^ o)).symm
          · rcases k2_cases with rfl | rfl | rfl | rfl
            · norm_num [←two_mul, pos]
            · exact (k1_ne_k2 rfl).elim
            · norm_num [abs_eq]
              exact (two_mul (q ^ o)).symm
            · norm_num [abs_eq]
              exact (two_mul (q ^ o)).symm
          · rcases k2_cases with rfl | rfl | rfl | rfl
            · simpa only [Fin.val_zero, zero_add, sub_zero, abs_pow, abs_eq, zero_sub, abs_neg] using (two_mul (q ^ o)).symm
            · simpa only [Fin.val_zero, zero_add, Prod.neg_mk, neg_zero, sub_zero, abs_neg,
                abs_pow, abs_eq, zero_sub] using (two_mul (q ^ o)).symm
            · exact (k1_ne_k2 rfl).elim
            · norm_num
              ring_nf
              norm_num [pos]
          · rcases k2_cases with rfl | rfl | rfl | rfl
            · simpa only [Fin.val_zero, zero_add, Prod.neg_mk, neg_zero, sub_zero, abs_pow,
                abs_eq, sub_neg_eq_add] using (two_mul (q ^ o)).symm
            · simpa only [Fin.val_zero, zero_add, Prod.neg_mk, neg_zero, sub_zero, abs_neg,
                abs_pow, abs_eq, sub_neg_eq_add] using (two_mul (q ^ o)).symm
            · simp only [Fin.val_zero, zero_add, Prod.neg_mk, neg_zero, sub_self, abs_zero,
                sub_neg_eq_add, ← two_mul, abs_eq_self, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left,
                pos]
            · exact (k1_ne_k2 rfl).elim

        -- and if we have some path r which is cardinal_{o, q}, then
        -- |r_x(i + 2) - r_x(x + 1)| + |r_y(i + 2) - r_y(x + 1)|
        -- = q ^ (i + 1 + o)
        have abs_2 (r : Fin (k + 2) → ℚ × ℚ) (hr : cardinal o q r) (i : Fin k)
          : |(r (i.succ.succ)).1 - (r (i.succ.castSucc)).1|
          + |(r (i.succ.succ)).2 - (r (i.succ.castSucc)).2| = q ^ (i.succ.val + o) := by
            obtain ⟨k2, h2, k2_cases⟩ := add_cases i.succ r hr
            rw [h2]
            norm_num
            rcases k2_cases with rfl | rfl | rfl | rfl
            all_goals norm_num [abs_eq]

        -- and if n is the last coordinate of r, then
        -- |r_x(n) - r_x(1)| + |r_y(n) - r_y(1)| ≤ ∑ i ∈ [0, k), q ^ (i + 1 + o)
        have abs_uppper (r : Fin (k + 2) → ℚ × ℚ) (hr : cardinal o q r)
          : |(r (Fin.last _)).1 - (r 1).1|
          + |(r (Fin.last _)).2 - (r 1).2|
          ≤ ∑ i : Fin k, q ^ (i.succ.castSucc.val + o) := by
            calc _
              -- write terms as telescoping sums
              _ = |∑ i : Fin k, ((r i.succ.succ).1 - (r i.castSucc.succ).1)|
                + |∑ i : Fin k, ((r i.succ.succ).2 - (r i.castSucc.succ).2)| := by
                  congr
                  · rw [sum_fin_sub (fun i : Fin (k + 1) => (r i.succ).1)]
                    norm_num
                  · rw [sum_fin_sub (fun i : Fin (k + 1) => (r i.succ).2)]
                    norm_num
              -- distribute abs
              _ ≤ ∑ i : Fin k, |((r i.succ.succ).1 - (r i.castSucc.succ).1)|
                + ∑ i : Fin k, |((r i.succ.succ).2 - (r i.castSucc.succ).2)| := by
                  gcongr <;> exact Finset.abs_sum_le_sum_abs _ _
              -- merge sums
              _ ≤ ∑ i : Fin k, (|((r i.succ.succ).1 - (r i.castSucc.succ).1)|
                                + |((r i.succ.succ).2 - (r i.castSucc.succ).2)|) := by
                  rw [Finset.sum_add_distrib]
              -- swap succ castSucc order
              _ = ∑ i : Fin k, (|((r i.succ.succ).1 - (r i.succ.castSucc).1)|
                                + |((r i.succ.succ).2 - (r i.succ.castSucc).2)|) := by congr
              -- termwise equal
              _ = ∑ i : Fin k, q ^ (i.succ.castSucc.val + o) := by simp [abs_2 r hr]

        -- using the triangle inequality we have
        -- 2 * q ^ o - 2 * (∑ i ∈ [0, k), q ^ (i + 1 + o))
        have abs_3 : 2 * q ^ o - 2 * (∑ i : Fin k, q ^ (i.succ.castSucc.val + o))
          ≤ |(r2' (Fin.last _)).1 - (r1' (Fin.last _)).1| + |(r2' (Fin.last _)).2 - (r1' (Fin.last _)).2| := by
            trans 2 * q ^ o - ((∑ i : Fin k, q ^ (i.succ.castSucc.val + o)) + (∑ i : Fin k, q ^ (i.succ.castSucc.val + o)))
            · refine le_of_eq ?_
              simp only [two_mul]

            trans 2 * q ^ o
              - ( (|(r1' (Fin.last _)).1 - (r1' 1).1| + |(r1' (Fin.last _)).2 - (r1' 1).2|)
                + (|(r2' (Fin.last _)).1 - (r2' 1).1| + |(r2' (Fin.last _)).2 - (r2' 1).2|))
            · gcongr
              · exact abs_uppper r1' h6
              · exact abs_uppper r2' h7

            rw [←abs_1]

            -- group x-axis and y-axis separately
            suffices : |(r2' 1).1 - (r1' 1).1| + |(r2' 1).2 - (r1' 1).2|
                  ≤ ( |(r2' (Fin.last (k + 1))).1 - (r2' 1).1|
                    + |(r2' (Fin.last (k + 1))).1 - (r1' (Fin.last (k + 1))).1|
                    + |(r1' (Fin.last (k + 1))).1 - (r1' 1).1|
                    )
                  + ( |(r2' (Fin.last (k + 1))).2 - (r2' 1).2|
                    + |(r2' (Fin.last (k + 1))).2 - (r1' (Fin.last (k + 1))).2|
                    + |(r1' (Fin.last (k + 1))).2 - (r1' 1).2|
                    )
            · linarith

            -- we use the triangle inequality for 3 pairs
            have triangle_four (a b c d : ℚ) : |a - d| ≤ |b - a| + |b - c| + |c - d| := by
              trans |a - c| + |c - d|
              · exact abs_sub_le a c d

              trans |a - b| + |b - c| + |c - d|
              · gcongr
                exact abs_sub_le a b c

              rw [abs_sub_comm a b]

            -- both the x-axis and y-axis inequality holds because of the triangle inequality
            gcongr <;> exact triangle_four _ _ _ _

        have lhs_eq_zero
          : |(r2' (Fin.last (k + 1))).1 - (r1' (Fin.last (k + 1))).1|
          + |(r2' (Fin.last (k + 1))).2 - (r1' (Fin.last (k + 1))).2|
          = 0 := by norm_num [h10]

        rw [lhs_eq_zero] at abs_3

        -- assume q = 1 / 2
        by_contra q_eq

        -- then the RHS is positive
        have rhs_pos : 0 < 2 * q ^ o - 2 * ∑ i : Fin k, q ^ (↑i.succ.castSucc + o) := by
          -- add ∑ i ∈ [0, k), q ^ (i + 1 + o) to both sides and divide by 2
          suffices : ∑ i : Fin k, q ^ (↑i.succ.castSucc + o) < q ^ o
          · linarith

          -- divide both sides by q ^ o = (1 / 2) ^ o
          rw [q_eq, ←one_mul ((1 / 2 : ℚ) ^ o), ←div_lt_iff₀ (by positivity), Finset.sum_div]

          -- then we just need to show that ∑ i ∈ [0, k), (1 / 2) ^ (i + 1) < 1
          convert_to ∑ i : Fin k, (1 / 2 : ℚ) ^ (↑i.succ.castSucc) < 1
          · congr
            ext i
            rw [div_eq_iff]
            exact pow_add (1 / 2) (↑i.succ.castSucc) o
            · exact pow_ne_zero o (by linarith only)

          -- add one to each index of the sum to get i ∈ [1, k + 1)
          simp only [Fin.coe_castSucc, Fin.val_succ]
          rw [←Finset.sum_range (fun i => (1 / 2) ^ (i + 1))]
          convert_to ∑ i ∈ Finset.Ico 1 (k + 1), (1 / 2 : ℚ) ^ i < 1
          · trans ∑ i ∈ Finset.Ico 0 k, (1 / 2) ^ (i + 1)
            · rw [Finset.range_eq_Ico]

            exact Finset.sum_Ico_add' ((1 / 2) ^ ·) 0 k 1

          -- then it's clearly a geometric sum, so we can write in closed form
          rw [geom_sum_Ico' (by linarith only) (by omega)]

          -- then it's just arithmetic
          ring_nf
          norm_num

        -- which is impossible
        linarith

    constructor
    -- first we'll show the conditions on the paths imply that q = 1
    · intro ⟨n, r1, r2, nee, first_eq, h1, h2, last_eq⟩

      -- r_1 and r_2 are both cardinal_{0, q}
      replace h1 : cardinal 0 q r1 := h1
      replace h2 : cardinal 0 q r2 := h2

      -- wlog, the paths start at (0, 0)
      wlog eq_zero : r1 0 = 0 generalizing r1 r2
      -- else just subtract r_1(0) = r_2(0) from both paths
      · let r1' : Fin (n + 1) → ℚ × ℚ := fun i => r1 i - r1 0
        let r2' : Fin (n + 1) → ℚ × ℚ := fun i => r2 i - r2 0
        apply this r1' r2'
        -- the paths are still not equal
        · simpa [r1', r2', funext_iff, first_eq] using nee
        · norm_num [r1', r2']
        · norm_num [r1', r2', first_eq, last_eq]
        · intro i
          norm_num [r1']
          rw [sub_add_eq_add_sub]
          rw [sub_add_eq_add_sub]
          rw [sub_right_comm _ (r1 0)]
          rw [sub_right_comm _ (r1 0)]
          simpa only [sub_left_inj, add_zero] using h1 i
        · intro i
          norm_num [r2']
          rw [sub_add_eq_add_sub]
          rw [sub_add_eq_add_sub]
          rw [sub_right_comm _ (r2 0)]
          rw [sub_right_comm _ (r2 0)]
          simpa only [sub_left_inj, add_zero] using h2 i
        · simp only [sub_self, r1']

      -- the paths are not moving identically in the x direction
      wlog not_all_x : ¬∀ i : Fin n,
        ((r1 (i.succ)).1 - (r1 i.castSucc).1) = ((r2 (i.succ)).1 - (r2 i.castSucc).1)
        generalizing r1 r2
      · norm_num at not_all_x
        -- else, swap x and y
        apply this (Prod.swap ∘ r1) (Prod.swap ∘ r2)
        · norm_num [funext_iff]
          exact Function.ne_iff.mp nee
        · simp only [Function.comp_apply, Prod.swap_inj]
          tauto
        · simpa only [Function.comp_apply, Prod.swap_inj] using last_eq
        · intro i
          simp only [Function.comp_apply, add_zero]
          rw [←Prod.swap_swap ((r1 i.castSucc).swap + (q ^ i.val, 0))]
          rw [←Prod.swap_swap ((r1 i.castSucc).swap - (q ^ i.val, 0))]
          rw [←Prod.swap_swap ((r1 i.castSucc).swap + (0, q ^ i.val))]
          rw [←Prod.swap_swap ((r1 i.castSucc).swap - (0, q ^ i.val))]
          rw [Prod.swap_add, Prod.swap_swap, Prod.swap_inj]
          rw [Prod.swap_sub, Prod.swap_swap, Prod.swap_inj]
          rw [Prod.swap_add, Prod.swap_swap, Prod.swap_inj]
          rw [Prod.swap_sub, Prod.swap_swap, Prod.swap_inj]
          rw [Prod.swap_prod_mk]
          specialize h1 i
          rw [add_zero] at h1
          tauto
        · intro i
          simp only [Function.comp_apply, add_zero]
          rw [←Prod.swap_swap ((r2 i.castSucc).swap + (q ^ i.val, 0))]
          rw [←Prod.swap_swap ((r2 i.castSucc).swap - (q ^ i.val, 0))]
          rw [←Prod.swap_swap ((r2 i.castSucc).swap + (0, q ^ i.val))]
          rw [←Prod.swap_swap ((r2 i.castSucc).swap - (0, q ^ i.val))]
          rw [Prod.swap_add, Prod.swap_swap, Prod.swap_inj]
          rw [Prod.swap_sub, Prod.swap_swap, Prod.swap_inj]
          rw [Prod.swap_add, Prod.swap_swap, Prod.swap_inj]
          rw [Prod.swap_sub, Prod.swap_swap, Prod.swap_inj]
          rw [Prod.swap_prod_mk]
          specialize h2 i
          rw [add_zero] at h2
          tauto
        · simpa [Prod.swap_eq_iff_eq_swap] using eq_zero
        · by_contra hh
          norm_num at hh
          have r1_eq_r2 : r1 = r2 := by
            apply @_root_.funext
            intro i
            induction' i using Fin.induction with i hi
            · tauto
            · specialize not_all_x i
              specialize hh i
              norm_num [hi] at not_all_x hh
              exact Prod.ext not_all_x hh
          contradiction

      -- we'll show that q can only be 1/2, 1 or 2
      have q_mem : q = 1 / 2 ∨ q = 1 ∨ q = 2 := by
        -- let A_x(n) be the x coordinate of the first ant after n steps
        let Ax : Fin (n + 1) → ℚ := fun i => (r1 i).1
        -- let B_x(n) be the x coordinate of the second ant after n steps
        let Bx : Fin (n + 1) → ℚ := fun i => (r2 i).1

        -- A_x(i + 1) - A_x(i) is q ^ i or -(q ^ i) or 0
        have sub_mem_A (i : Fin n) :
          (Ax (i.succ) - Ax i.castSucc) ∈ ({q ^ i.val, -q ^ i.val, 0} : Finset ℚ)
          := by
            unfold Ax
            rcases h1 i with hh | hh | hh | hh <;> norm_num [hh]
        replace sub_mem_A (i : Fin n) :
          (Ax (i.succ) - Ax i.castSucc) = q ^ i.val
          ∨ (Ax (i.succ) - Ax i.castSucc) = -q ^ i.val
          ∨ (Ax (i.succ) - Ax i.castSucc) = 0
          := by simpa only [Finset.mem_insert, Finset.mem_singleton] using sub_mem_A i

        -- B_x(i + 1) - B_x(i) is q ^ i or -(q ^ i) or 0
        have sub_mem_B (i : Fin n) :
          (Bx (i.succ) - Bx i.castSucc) ∈ ({q ^ i.val, -q ^ i.val, 0} : Finset ℚ)
          := by
            unfold Bx
            rcases h2 i with hh | hh | hh | hh <;> norm_num [hh]
        replace sub_mem_B (i : Fin n) :
          (Bx (i.succ) - Bx i.castSucc) = q ^ i.val
          ∨ (Bx (i.succ) - Bx i.castSucc) = -q ^ i.val
          ∨ (Bx (i.succ) - Bx i.castSucc) = 0
          := by simpa only [Finset.mem_insert, Finset.mem_singleton] using sub_mem_B i

        -- let Az(i) represent the sign of A_x(i + 1) - A_x(i)
        -- -1, 0 or 1
        let Az : Fin n → ℤ := by
          intro i
          by_cases pos  : (Ax (i.succ) - Ax i.castSucc) = q ^ i.val; exact 1
          by_cases neg  : (Ax (i.succ) - Ax i.castSucc) = -(q ^ i.val); exact -1
          exact 0

        -- let Bz(i) represent the sign of B_x(i + 1) - B_x(i)
        -- -1, 0 or 1
        let Bz : Fin n → ℤ := by
          intro i
          by_cases pos  : (Bx (i.succ) - Bx i.castSucc) = q ^ i.val; exact 1
          by_cases neg  : (Bx (i.succ) - Bx i.castSucc) = -(q ^ i.val); exact -1
          exact 0

        -- Az(i) can only be -1, 0 or 1
        have A_coeffs (i : Fin n) : Az i ∈ ({-1, 0, 1} : Finset ℤ) := by
          specialize sub_mem_A i
          simp only [Int.reduceNeg, dite_eq_ite, Finset.mem_insert, Finset.mem_singleton,
            ite_eq_left_iff, Az]
          split_ifs with hpos
          all_goals
          · simp only [hpos, one_ne_zero, imp_false, not_not, false_or, zero_ne_one, Int.reduceNeg, true_or, or_true]

        -- Bz(i) can only be -1, 0 or 1
        have B_coeffs (i : Fin n) : Bz i ∈ ({-1, 0, 1} : Finset ℤ) := by
          specialize sub_mem_B i
          simp only [Int.reduceNeg, dite_eq_ite, Finset.mem_insert, Finset.mem_singleton,
            ite_eq_left_iff, Bz]
          split_ifs with hpos
          all_goals
          · simp only [hpos, one_ne_zero, imp_false, not_not, false_or, zero_ne_one, Int.reduceNeg, true_or, or_true]

        -- let P_A be the polynomial where X^i has coefficient Az(i)
        let PA : ℤ[X] := ∑ i : Fin n, C (Az i) * X ^ (i.val)

        -- and P_B be the polynomial where X^i has coefficient Bz(i)
        let PB : ℤ[X] := ∑ i : Fin n, C (Bz i) * X ^ (i.val)

        -- then the final value of Ax is equal to P_A(q)
        have as_poly_A : Ax (Fin.last n) = PA.eval₂ (Int.castRingHom ℚ) q := by
          trans Ax (Fin.last n) - Ax 0
          · have ax_zero : Ax 0 = 0 := by
              norm_num [Ax, eq_zero]
            linarith
          rw [←sum_fin_sub Ax, Polynomial.eval₂_finset_sum]
          congr
          ext i
          simp only [Fin.val_succ, eval₂_mul, eval₂_X_pow, Polynomial.eval₂_C]
          norm_num [Az]
          specialize sub_mem_A i
          split_ifs with h1 h2 <;> tauto

        -- and the final value of Bx is equal to B_A(q)
        have as_poly_B : Bx (Fin.last n) = PB.eval₂ (Int.castRingHom ℚ) q := by
          trans Bx (Fin.last n) - Bx 0
          · have bx_zero : Bx 0 = 0 := by
              norm_num [←first_eq, Bx, eq_zero]
            linarith
          rw [←sum_fin_sub Bx, Polynomial.eval₂_finset_sum]
          congr
          ext i
          simp only [Fin.val_succ, eval₂_mul, eval₂_X_pow, Polynomial.eval₂_C]
          norm_num [Bz]
          specialize sub_mem_B i
          split_ifs with h1 h2 <;> tauto

        -- now consider P = P_A - P_B
        let P : ℤ[X] := PA - PB

        -- if P is zero, then Az(i) = Bz(i) for every i
        have of_P_eq_zero (h : P = 0) (i : Fin n) : Az i = Bz i := by
          unfold P at h
          rw [sub_eq_zero, Polynomial.ext_iff] at h
          specialize h i
          simpa [PA, PB, ←Fin.ext_iff] using h

        -- so P is non-zero
        have P_ne_zero : P ≠ 0 := by

          -- assume it was zero
          by_contra hh
          norm_num at not_all_x
          obtain ⟨i, ih⟩ := not_all_x
          specialize of_P_eq_zero hh i
          norm_num [Az, Bz] at of_P_eq_zero
          specialize sub_mem_A i
          specialize sub_mem_B i
          replace ih : Ax i.succ - Ax i.castSucc ≠ Bx i.succ - Bx i.castSucc := ih
          have q_ne1 : ¬(-q ^ i.val = q ^ i.val)
            := CharZero.neg_eq_self_iff.mp.mt <| pow_ne_zero i (by positivity)
          have q_ne2 : ¬(0 = q ^ i.val) := (pow_ne_zero i (by positivity)).symm
          have q_ne3 : ¬(q = 0) := by positivity

          rcases sub_mem_A with ha | ha | ha
          <;> rcases sub_mem_B with hb | hb | hb
              <;> norm_num [ha, hb, q_ne1, q_ne2, q_ne3] at of_P_eq_zero ih

        -- so P(q) = 0
        have P_q : P.eval₂ (Int.castRingHom ℚ) q = 0 := by
          simp only [eval₂_sub, ← as_poly_A, last_eq, ← as_poly_B, sub_self, P, Ax, Bx]

        -- every coefficient of P is either -2, -1, 0, 1 or 2
        have P_coeff (i : ℕ) : P.coeff i ∈ ({-2, -1, 0, 1, 2} : Finset ℤ) := by
          simp only [Int.reduceNeg, eq_intCast, coeff_sub, finset_sum_coeff, coeff_intCast_mul,
            Int.cast_id, coeff_X_pow, mul_ite, mul_one, mul_zero, Finset.mem_insert,
            Finset.mem_singleton, P, PA, PB]

          -- consider every coefficient less than n
          by_cases ih : i < n
          · have e_eq : i = (⟨i, ih⟩ : Fin n) := by rfl
            rw [e_eq]
            have iff (x : Fin n) : i = ↑x ↔ ⟨i, ih⟩ = x := by
              rw [Fin.ext_iff]
            simp_rw [iff]

            simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Int.reduceNeg]
            specialize A_coeffs ⟨i, ih⟩
            specialize B_coeffs ⟨i, ih⟩
            norm_num at A_coeffs B_coeffs
            rcases A_coeffs with aa | aa | aa
            <;> (rcases B_coeffs with bb | bb | bb <;> norm_num [aa, bb])

          -- the rest are zero
          · norm_num at ih
            have ne (x : Fin n) : ¬(i = x) := by
              have x_lt : x.val < n := x.isLt
              linarith
            norm_num [ne]

        -- if the "trailing degree" of P is i, then let P = X ^ i * Q, where Q is P / X ^ i
        -- then the 0th coefficient of Q is the trailing coefficient of P
        -- and the leading coefficient of Q is the leading coefficient of P
        obtain ⟨Q, hQ1, hQ2, hQ3⟩
          : ∃ Q, (X ^ P.natTrailingDegree * Q = P) ∧ Q.coeff 0 = P.trailingCoeff ∧ Q.leadingCoeff = P.leadingCoeff := by
            let Q : ℤ[X] := ∑ n ∈ P.support, (C (P.coeff n) * X ^ (n - P.natTrailingDegree))
            exists Q
            by_cases P_eq_zero : P = 0
            · norm_num [P_eq_zero, Q]
            have left : X ^ P.natTrailingDegree * Q = P := by
              unfold Q
              rw [Finset.mul_sum]
              trans ∑ i ∈ P.support, (C (P.coeff i) * X ^ i)
              · apply Finset.sum_congr rfl
                intro i ih
                ring_nf
                have ne_zero : ¬(P.coeff i = 0) := mem_support_iff.mp ih
                have le_i : P.natTrailingDegree ≤ i := natTrailingDegree_le_of_mem_supp i ih
                field_simp [ne_zero, ←pow_add]
              rw [←as_sum_support_C_mul_X_pow P]
            split_ands
            · exact left
            · rw [←left, Polynomial.trailingCoeff_mul]
              simp only [trailingCoeff, natTrailingDegree_X_pow, coeff_X_pow, ↓reduceIte, one_mul]
              congr 1
              rw [Eq.comm, Polynomial.natTrailingDegree_eq_zero]
              apply Decidable.or_iff_not_imp_left.mpr
              intro Q_zero
              simp only [eq_intCast, finset_sum_coeff, mul_coeff_zero, intCast_coeff_zero, Int.cast_id,
                coeff_X_pow, mul_ite, mul_one, mul_zero, ne_eq, Q]
              convert_to (∑ x ∈ P.support, if x = P.natTrailingDegree then P.coeff x else 0) ≠ 0
              · refine Eq.congr ?_ rfl
                apply Finset.sum_congr rfl
                intro i ih
                congr 1
                rw [eq_iff_iff, Eq.comm, Nat.sub_eq_zero_iff_le]
                exact LE.le.le_iff_eq <| natTrailingDegree_le_of_mem_supp i ih
              simp only [P_eq_zero, Finset.sum_ite_eq', mem_support_iff, ne_eq, coeff_natTrailingDegree_eq_zero,
                not_false_eq_true, ↓reduceIte]
            · rw [←left]
              simp only [leadingCoeff_mul, monic_X_pow, Monic.leadingCoeff, one_mul]

        -- Using the rational root theorem we have that q divides the trailing and leading coefficient of P
        have ⟨dvd_last, dvd_first⟩ : q.num ∣ P.trailingCoeff ∧ q.den ∣ P.leadingCoeff.natAbs := by
          -- when considering a rational number as an element of a fraction ring, then either the
          -- numerator and denomintor are as expected, or their sign is flipped
          have IsFractionRing_rat_num_den (q : ℚ)
            : (IsFractionRing.num ℤ q) = q.num ∧ (IsFractionRing.den ℤ q) = (q.den : ℤ)
            ∨ -(IsFractionRing.num ℤ q) = q.num ∧ -(IsFractionRing.den ℤ q) = (q.den : ℤ)
            := by
              have div_eq : (IsFractionRing.num ℤ q) / (IsFractionRing.den ℤ q) = q := by
                nth_rw 3 [←IsFractionRing.mk'_num_den ℤ q]
                simp only [IsFractionRing.mk'_eq_div, algebraMap_int_eq, eq_intCast]
              have ne_zero := nonZeroDivisors.coe_ne_zero (IsFractionRing.den ℤ q)

              refine (lt_or_gt_of_ne ne_zero.symm).imp ?_ ?_
              all_goals
              · intro aa
                refine Rat.div_int_inj (by omega) (by positivity) ?_ q.reduced ?_
                · simpa only [Int.natAbs_neg]
                    using Int.coprime_iff_nat_coprime.mp <| (IsFractionRing.num_den_reduced ℤ q).isCoprime
                · simp only [div_eq, Int.cast_natCast, Rat.num_div_den q, Int.cast_neg,
                  neg_div_neg_eq, div_eq, Rat.num_div_den q]

          -- so the absolute value of the denominator and numerator are what we expect
          have IsFractionRing_rat_den_natAbs (q : ℚ) : ((IsFractionRing.den ℤ q) : ℤ).natAbs = q.den := by
            rcases IsFractionRing_rat_num_den q with ⟨_, hh⟩ | ⟨_, hh⟩
            <;> simpa using congrArg Int.natAbs hh
          have IsFractionRing_rat_num_natAbs (q : ℚ) : ((IsFractionRing.num ℤ q) : ℤ).natAbs = q.num.natAbs := by
            rcases IsFractionRing_rat_num_den q with ⟨hh, _⟩ | ⟨hh, _⟩
            <;> simpa using congrArg Int.natAbs hh

          -- so we have the rational root theorem, that if r = a / b is a root of some integer polynomial p
          -- then |a| divides the 0th coefficient...
          have num_dvd_of_is_root_standard_case {p : ℤ[X]} {r : ℚ}
            (H : p.aeval r = 0) :
            r.num.natAbs ∣ (p.coeff 0).natAbs := by
              simpa [←Int.natAbs_dvd_natAbs, IsFractionRing_rat_num_natAbs r] using num_dvd_of_is_root H

          -- ...and b divides the leading coefficeint
          have den_dvd_of_is_root_standard_case {p : ℤ[X]} {r : ℚ}
              (H : p.aeval r = 0) :
              r.den ∣ p.leadingCoeff.natAbs := by
            simpa [←Int.natAbs_dvd_natAbs, IsFractionRing_rat_den_natAbs r] using den_dvd_of_is_root H
          rw [←hQ2, ←hQ3]

          -- in our case, q is a root of Q
          have mem_roots : Q.aeval q = 0 := by
            rw [←hQ1] at P_q
            norm_num at P_q
            rcases P_q with hh | hh
            -- but q is positive
            · linarith
            · exact hh

          -- so we can apply the rational root theorem to Q
          split_ands
          · exact Int.natAbs_dvd_natAbs.mp (num_dvd_of_is_root_standard_case mem_roots)
          · exact den_dvd_of_is_root_standard_case mem_roots

        -- the trailing coefficient is -2, -1, 1 or 2
        have trailing_cases : P.trailingCoeff ∈ ({-2, -1, 1, 2} : Finset ℤ) := by
          convert_to P.trailingCoeff ∈ ({-2, -1, 0, 1, 2} : Finset ℤ).erase 0
          rw [Finset.mem_erase]
          split_ands
          · exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr P_ne_zero
          · exact P_coeff (P.natTrailingDegree)

        -- and the leading coefficient is also -2, -1, 1 or 2
        have leading_cases : P.leadingCoeff ∈ ({-2, -1, 1, 2} : Finset ℤ) := by
          convert_to P.leadingCoeff ∈ ({-2, -1, 0, 1, 2} : Finset ℤ).erase 0
          rw [Finset.mem_erase]
          split_ands
          · exact Polynomial.leadingCoeff_ne_zero.mpr P_ne_zero
          · exact P_coeff (P.natDegree)

        -- so the numerator of q divides 2
        have q_num_dvd_two : q.num ∣ 2 := by
          refine dvd_last.trans ?_
          norm_num at trailing_cases
          rcases trailing_cases with hh | hh | hh | hh <;> norm_num [hh]

        -- and the denominator too
        have q_den_dvd_two : q.den ∣ 2 := by
          refine dvd_first.trans ?_
          norm_num at leading_cases
          rcases leading_cases with hh | hh | hh | hh <;> norm_num [hh]

        -- so both are at most 2
        have den_le : q.den ≤ 2 := Nat.le_of_dvd (by omega) q_den_dvd_two
        have num_le : q.num ≤ 2 := Int.le_of_dvd (by omega) q_num_dvd_two

        -- and the numberator is at least -2
        have le_num : -2 ≤ q.num := by
          suffices : -q.num ≤ 2
          · omega

          have neg_dvd : -q.num ∣ 2 := Int.neg_dvd.mpr q_num_dvd_two
          exact Int.le_of_dvd (by omega) neg_dvd

        -- so the denomintor is 1 or 2
        have q_den_cases : q.den ∈ ({1, 2} : Finset ℕ) := by
          norm_num
          interval_cases hd : q.den <;> norm_num at hd ⊢

        -- and the numerator is also 1 or 2
        have q_num_cases : q.num ∈ ({1, 2} : Finset ℤ) := by
          norm_num at hq
          rw [←Rat.num_pos] at hq
          norm_num
          interval_cases hn : q.num
          all_goals
          · norm_num at hn ⊢

        rw [←Rat.num_div_den q]
        simp only [Finset.mem_insert, Finset.mem_singleton] at q_den_cases q_num_cases

        -- consider cases, we see that q is 1/2, 1 or 2
        rcases q_den_cases with hd | hd
        <;> simp only [hd, Finset.mem_insert, Finset.mem_singleton]
        <;> rcases q_num_cases with hn | hn <;> simp [hn]

      -- assume n is zero
      by_cases n_eq_zero : n = 0
      · subst n_eq_zero

        -- then r_1 = r_2
        have eqq : r1 = r2 := by
          apply @_root_.funext
          intro i
          fin_cases i
          norm_num [first_eq]
        contradiction

      -- so assume n is non-zero

      -- so set n = n + 1
      obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := Nat.exists_eq_succ_of_ne_zero n_eq_zero

      -- consider possible values of q
      rcases q_mem with eq_half | eq_one | eq_two
      -- we've already proven that q ≠ 1 / 2
      · exact absurd eq_half <| q_half q hq (n + 1) r1 r2 nee first_eq h1 h2 last_eq

      -- q = 1 works
      · exact eq_one

      -- we'll show that a solution where q = 2 implies a solution for q = 1 / 2
      -- we scale the plane by 2 ^ n to get new paths which are the reverse of r_1 and r_2
      · let r1' : Fin (n + 1 + 1) → ℚ × ℚ
          := (fun i => (q ^ n)⁻¹ • (r1 i.rev))
        let r2' : Fin (n + 1 + 1) → ℚ × ℚ
          := (fun i => (q ^ n)⁻¹ • (r2 i.rev))

        -- the first coordinates are still the same
        have r1_eq_r2_first : r1' 0 = r2' 0 := by
          norm_num [r1', r2', last_eq]

        -- and the last too
        have r1_eq_r2_last : r1' (Fin.last _) = r2' (Fin.last _) := by
          norm_num [r1', r2', first_eq]

        -- if we have some path r which is cardinal_{0, 2}, then scaling by 2 ^ n and taking
        -- the reverse will give us a path r' which is cardinal_{0, 1/2}.
        have cardinal_rev (r : Fin (n + 1 + 1) → ℚ × ℚ) (hr : cardinal 0 q r)
          : cardinal 0 (1 / 2) (fun i => (q ^ n)⁻¹ • (r i.rev)) := by
          norm_num [cardinal, Fin.rev_castSucc, Fin.rev_succ]
          intro i
          specialize hr i.rev
          norm_num at hr

          have prod_eq : (2 ^ n)⁻¹ * 2 ^ (n + 1 - (i + 1))
            = (1 / 2 : ℚ) ^ i.val := by
              -- rearrange
              field_simp
              -- combine powers
              rw [←pow_add]
              -- exponents are equal to both sides are equal
              congr
              omega

          subst eq_two
          rcases hr with hh | hh | hh | hh <;> norm_num [hh, smul_add, smul_sub, prod_eq]

        -- so r'_1 and r'_2 are both `cardinal_{0, 1/2}`
        have h1 : cardinal 0 (1 / 2) r1' := cardinal_rev r1 h1
        have h2 : cardinal 0 (1 / 2) r2' := cardinal_rev r2 h2

        -- the paths are not identical
        have r1_ne_r2 : r1' ≠ r2' := by
          norm_num [r1', r2']
          -- scaling is injective
          have map_inj : Function.Injective <| (((q ^ n)⁻¹ • ·) : ℚ × ℚ → ℚ × ℚ)
            := smul_right_injective (ℚ × ℚ) (by positivity)
          norm_num [funext_iff]
          simp_rw [map_inj.ne_iff]

          -- so if r_1 and r_2 differ at some timestep x...
          obtain ⟨x, xh⟩ := Function.ne_iff.mp nee

          -- ...then r'_1 and r'_2 differ at -x from the end
          exists x.rev
          simpa using xh

        -- then we have valid paths where q = 1 / 2, but we already proved that's impossible
        have := q_half (1 / 2) (by positivity) (n + 1) r1' r2' r1_ne_r2
          r1_eq_r2_first h1 h2 r1_eq_r2_last
        contradiction

    -- we show that there exists paths for q = 1
    · rintro rfl

      -- the ants can start at (0, 0) and one ant walks east then north, while the other walks north then east
      exists 2, ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]
      split_ands
      -- the paths are not equal
      · decide
        -- first coordinate is equal
      · rfl
      -- each step is either north, east, south or west
      · intro i
        fin_cases i <;> norm_num
      · intro i
        fin_cases i <;> norm_num
        -- last coordinate is equal
      · rfl
