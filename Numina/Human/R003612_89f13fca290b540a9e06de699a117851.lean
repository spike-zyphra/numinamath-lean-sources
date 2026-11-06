import Mathlib

/- The square root of 4 is 2. -/
lemma Real_sqrt_four_eq_two : √(4 : ℝ) = 2 := by
  convert_to √(2 * 2) = 2
  · norm_num
  exact Real.sqrt_mul_self (by positivity)

/- x * 2 + √(6 - x) is strictly monotone if 2 < x. -/
lemma x_sq_sub_sqrt_six_sub_mono_on : StrictMonoOn (fun x => x * 2 + √(6 - x)) (Set.Iic (2 : ℝ)) := by
  intro a ah b bh ab
  -- simplify
  simp only [Set.mem_Iic] at ah bh ⊢

  -- rewrite a = 6 - a', b = 6 - b'
  obtain ⟨a', rfl⟩ : ∃ a', a = 6 - a' := by exists 6 - a; norm_num
  obtain ⟨b', rfl⟩ : ∃ b', b = 6 - b' := by exists 6 - b; norm_num
  ring_nf

  -- then 4 ≤ a', b'
  replace ah : 4 ≤ a' := by linarith
  replace bh : 4 ≤ b' := by linarith

  -- reordering we find that we just need to show that (√a' - √b') * (√a' + √b' - 1) is nonnegative
  suffices : 0 ≤ (√a' - √b') * (√a' + √b' - 1)
  · ring_nf at this
    field_simp at this
    linarith

  -- we have that b' ≤ a'
  have b_le_a : b' ≤ a' := by linarith

  -- so the left term is positive
  have left_pos : 0 ≤ (√a' - √b') := by
    simpa only [sub_nonneg] using Real.sqrt_le_sqrt b_le_a

  -- amd the right term is positive
  have right_pos : 0 ≤ (√a' + √b' - 1) := by
    have sqrt_a : √4 ≤ √a' := Real.sqrt_le_sqrt ah
    have sqrt_b : √4 ≤ √b' := Real.sqrt_le_sqrt bh

    rw [Real_sqrt_four_eq_two] at sqrt_a sqrt_b
    linarith

  positivity

/- The square root is strictly monotone on non-negative reals. -/
lemma Real_sqrt_strictmono_on : StrictMonoOn Real.sqrt (Set.Ici 0) := by
  intro a ah b bh ltt
  exact Real.sqrt_lt_sqrt ah ltt

/- If a function f is strictly monotone on the non-negative reals, and only takes non-negative values,
   then the iteration of f is also strictly monotone. -/
lemma StrictMonoOn_pos_iterate (f : ℝ → ℝ) (h1 : ∀ x, 0 ≤ f x) (h2 : StrictMonoOn f (Set.Ici 0)) (n : ℕ)
  : StrictMonoOn f^[n] (Set.Ici 0) := by
    induction' n with h3 h4
    · simp only [Function.iterate_zero]
      exact strictMonoOn_id
    · intro a ha b hb ltt
      simp only [Function.iterate_succ, Function.comp_apply]
      apply h4
      · exact h1 a
      · exact h1 b
      exact h2 ha hb ltt

/- Find all solutions to the following system of equations


$$

y=x+\sqrt{x+\sqrt{x+\sqrt{x+\ldots+\sqrt{x+\sqrt{y}}}}}, \quad x+y=6

$$


where there are 1974 square root signs in the equation. -/
theorem algebra_201524 {x y : ℝ}
    : ((x + y = 6) ∧ y = (fun i => x + √i)^[1974] y ∧ (∀ i < 1974, 0 ≤ (fun i => x + √i)^[i] y) ∧ (0 ≤ y))
    ↔ (x = 2 ∧ y = 4) := by

    -- we let n + 1 = 1974
    rw [show 1974 = 1973 + 1 by omega]
    generalize hh : 1973 = n

    -- consider when y is negative
    by_cases hx : y < 0
    -- then both cases are false
    · have y_ne : ¬y = 4 := by linarith
      have not_le : ¬0 ≤ y := by linarith

      norm_num [y_ne, not_le]

    -- so assume y is non-negative
    replace hx : 0 ≤ y := by linarith

    -- simplify
    simp only [hx, and_true]

    -- we show both directions separately
    constructor
    · intro ⟨eq_six, iter_eq, sqrt_pos⟩
      -- then y = 6 - x
      have y_eq : y = 6 - x := by linarith

      -- replace y everywhere
      subst y_eq

      -- then we have that x ≤ 6
      have x_le : x ≤ 6 := by linarith

      -- Then we have 6 = (x + √(x + √(... + √(6 - x)))) + x with n + 1
      replace iter_eq : 6 = (fun nn => (x + √·)^[nn] (6 - x) + x) (n + 1) := by
        simp only [Function.iterate_succ, Function.comp_apply] at iter_eq ⊢
        linarith

      -- we'll show that x = 2
      suffices : x = 2
      · norm_num [this]


      -- split on ordering of x and 2
      rcases lt_trichotomy x 2 with lee | eqq | gtt
      -- when x < 2, then x * 2 + √(6 - x) < 6
      · have pow_sub_lt_six : x * 2 + √(6 - x) < 6 := by
          -- rewrite RHS as 2 * 2 + √(6 - 2)
          convert_to (fun i => i * 2 + √(6 - i)) x < (fun i => i * 2 + √(6 - i)) 2
          · norm_num [Real_sqrt_four_eq_two]

          -- use that x * 2 + √(6 - x) is strictly monotone when x ≤ 2
          apply x_sq_sub_sqrt_six_sub_mono_on
          · exact le_of_lt lee
          -- 2 ≤ 2
          · norm_num
          · exact lee

        -- and (x + √(x + √(... + √(6 - x)))) + x is antitone in the number of square roots
        have f_mono : Antitone (fun nn => (x + √·)^[nn] (6 - x) + x) := by
          refine antitone_nat_of_succ_le ?_
          intro n
          induction' n with h1 h2
          · norm_num
            ring_nf
            -- in the base case we use that x * 2 + √(6 - x) ≤ 6
            exact le_of_lt pow_sub_lt_six
          -- we expand iterations to apply the induction hypothesis
          · simp only [add_le_add_iff_right] at h2 ⊢
            rw [Function.iterate_succ_apply']
            nth_rw 2 [Function.iterate_succ_apply']
            simp only [add_le_add_iff_left]

            -- apply induction hypothesis
            exact Real.sqrt_le_sqrt h2

        -- so (x + √(x + √(... + √(6 - x)))) + x is less than 6
        have le : (fun nn => (x + √·)^[nn] (6 - x) + x) (n + 1) < 6 := by
          -- if n was zero, then the inequality would follow
          have zeroth_lt : (fun nn => (x + √·)^[nn] (6 - x) + x) 1 < 6 := by
            norm_num
            ring_nf
            exact pow_sub_lt_six

          -- we that the function is antitone is number of square roots
          refine lt_of_le_of_lt ?_ zeroth_lt
          apply f_mono
          omega

        -- but then it can't be equal to 6, contradiction
        linarith
      -- x = 2 works
      · exact eqq
      -- when 2 < x
      -- and (x + √(x + √(... + √(6 - x)))) + x is strictly monotone in the number of square roots
      · have f_mono : StrictMono (fun nn => (x + √·)^[nn] (6 - x) + x) := by
          refine strictMono_nat_of_lt_succ ?_
          intro n
          -- simplify
          norm_num

          -- x + √i is strictly monotone over i, when i is a non-negative real
          have inner_mono : StrictMonoOn (x + √·) (Set.Ici 0)
            -- √i is strictly monotone, and adding a constant doesn't change that
            := MonotoneOn.add_strictMono monotoneOn_const Real_sqrt_strictmono_on

          -- (x + √(x + √(... + √i))) + x is strictly monotone over i, when i is a non-negative real
          have iterated_mono : StrictMonoOn (x + √·)^[n] (Set.Ici 0) := by
            apply StrictMonoOn_pos_iterate
            intro i
            positivity
            exact inner_mono

          apply iterated_mono
          -- 6 - x is non-negative
          · simpa only [Set.mem_Ici, sub_nonneg] using x_le

          -- x + √(6 - x) is non-negative
          · simp only [Set.mem_Ici]
            positivity
          -- we'll show 6 - x < x + √(6 - x)
          -- i.e. 6 < 2 * x + √(6 - x)
          · suffices hn : 6 < 2 * x + √(6 - x)
            · linarith

            -- consider the endpoint when x = 6
            by_cases x_eq_six : x = 6
            · subst x_eq_six

              -- then it's true
              norm_num

            -- so assume x < 6
            replace x_le : x < 6 := lt_of_le_of_ne x_le x_eq_six

            -- consider when 3 < x
            by_cases hxx : 3 < x
            -- then the inequality is clear
            · trans 2 * 3 + √(6 - x)
              · norm_num
                linarith
              · gcongr
            -- so let x ≤ 3
            · simp only [not_lt] at hxx

              -- then we'll show 6 - 2 * x < √(6 - x)
              suffices : 6 - 2 * x < √(6 - x)
              · linarith

              -- square both sides
              rw [←sq_lt_sq₀]

              -- simplify
              rw [Real.sq_sqrt hx]
              ring_nf

              -- then we have a quadratic x ^ 2 * 4 - x * 23 + 30, which we'll show is negative
              suffices : x ^ 2 * 4 - x * 23 + 30 < 0
              · linarith

              -- it has the roots 2 and 15 / 4, so we just need to show that
              -- (x - 2) * (x - 15 / 4) is negative
              suffices : (x - 2) * (x - 15 / 4) < 0
              · linarith

              -- the left factor is positive
              have left_pos : 0 < (x - 2) := by linarith
              -- the left factor is negative
              have right_pos : (x - 15 / 4) < 0 := by linarith

              -- so their product is positive
              exact mul_neg_of_pos_of_neg left_pos right_pos

              -- when squaring we used that both sides were positive
              · linarith
              · positivity

        -- so (x + √(x + √(... + √(6 - x)))) + x is greater than 6
        have lt : 6 < (fun nn => (x + √·)^[nn] (6 - x) + x) (n + 1) := by
          convert_to (fun nn => (x + √·)^[nn] (6 - x) + x) 0 < _
          · norm_num

          apply f_mono
          exact Nat.zero_lt_succ n

        -- but then it can't be equal to 6, contradiction
        linarith

    -- then we'll show that x = 2, y = 4 works
    · rintro ⟨rfl, rfl⟩
      norm_num [Real_sqrt_four_eq_two]

      -- we prove the result for general n
      clear hh

      -- prove properties separately
      split_ands
      -- we prove the equality by induction on n
      · induction' n with h1 h2
        · norm_num
        · rw [Function.iterate_succ_apply']
          norm_num [←h2, Real_sqrt_four_eq_two]
      -- every square roots is positive
      · intro i ih
        -- we prove by induction on number of square roots
        induction' i with h1 h2
        -- no square roots is positive
        · norm_num
        · rw [Function.iterate_succ_apply']
          positivity