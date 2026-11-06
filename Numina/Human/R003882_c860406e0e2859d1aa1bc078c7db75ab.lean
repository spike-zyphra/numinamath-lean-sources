import Mathlib

open Real

/- Expression with √2 can be simplified: √(2 + √2) ^ 2 = 2 + √2. -/
lemma sqrt_two_add_sqrt_two_sq : √(2 + √2) ^ 2 = 2 + √2 := sq_sqrt (by positivity)

/- Expression with √2 can be simplified: √(2 + √2) ^ 3 = (2 + √2) * √(2 + √2). -/
lemma sqrt_two_add_sqrt_two_pow_three : √(2 + √2) ^ 3 = (2 + √2) * √(2 + √2) := by
  rw [pow_succ', sqrt_two_add_sqrt_two_sq]
  ring

/- Expression with √2 is positive: 0 ≤ 2 - √2 -/
lemma two_sub_sqrt_two_pos : 0 ≤ 2 - √2 := by
  simp only [sub_nonneg]
  refine (sqrt_le_left ?_).mpr ?_
  · positivity
  · norm_num

/- Expression with √2 can be simplified: √(2 - √2) ^ 2 = 2 - √2. -/
lemma sqrt_two_sub_sqrt_two_sq : √(2 - √2) ^ 2 = 2 - √2 := sq_sqrt two_sub_sqrt_two_pos

/- Expression with √2 can be simplified: √(2 - √2) ^ 3 = (2 - √2) * √(2 - √2). -/
lemma sqrt_two_sub_sqrt_two_pow_three : √(2 - √2) ^ 3 = (2 - √2) * √(2 - √2) := by
  rw [pow_succ', sqrt_two_sub_sqrt_two_sq]
  ring

/- Specific values of sinus are equal to similar values of cosinus.
   sin (π / 8 + k * π / 2) = cos (3 * (π / 8 + k * π / 2) -/
lemma Real_sin_eq_cos_three_mul (k : ℤ)
  : Real.sin (π / 8 + k * π / 2) = Real.cos (3 * (π / 8 + k * π / 2)) := by
    -- remove angle multiples
    rw [Real.cos_three_mul]

    -- consider parity of k
    rcases Int.even_or_odd' k with ⟨k, rfl | rfl⟩
    -- then the angle is equal to π / 8 + k * π
    · have angle_eq : π / 8 + ↑(2 * k) * π / 2 = π / 8 + k * π := by
        push_cast
        ring

      -- unfold sinus and cosinus
      rw [angle_eq, Real.sin_add_int_mul_pi, Real.cos_add_int_mul_pi,
        Real.sin_pi_div_eight, Real.cos_pi_div_eight]

      -- the parity of k doesn't matter, we can simplify the equation to
      -- √(2 - √2) * (1 / 2) = √(2 + √2) * (-3 / 2) + √(2 + √2) ^ 3 * (1 / 2)
      suffices he : √(2 - √2) * (1 / 2) = √(2 + √2) * (-3 / 2) + √(2 + √2) ^ 3 * (1 / 2)
      · rcases Int.even_or_odd' k with ⟨k, rfl | rfl⟩
        -- when k is even
        · have k_even : Even (2 * k) := even_two_mul k
          have pow_eq_one : (-1 : ℝ) ^ (2 * k) = 1 := Even.neg_one_zpow k_even
          -- simplify
          norm_num [pow_eq_one]
          ring_nf
          exact he
        -- when k is odd
        · have k_odd : Odd (2 * k + 1) := odd_two_mul_add_one k
          have pow_eq_neg_one : (-1 : ℝ) ^ (2 * k + 1) = -1 := Odd.neg_one_zpow k_odd
          -- simplify
          rw [←neg_inj]
          norm_num [pow_eq_neg_one]
          ring_nf
          exact he

      -- simplify
      norm_num [sqrt_two_add_sqrt_two_pow_three]

      -- square both sides
      rw [←sq_eq_sq₀]

      -- simplify
      ring_nf
      norm_num [sqrt_two_add_sqrt_two_sq, sqrt_two_sub_sqrt_two_sq]
      ring_nf
      norm_num
      ring
      -- when squaring, we assumed both sides were positive
      · positivity
      · convert_to 0 ≤ √(2 + √2) * (√2 - 1) * (1 / 2)
        · ring_nf
        have sub_one_nonneg : 0 ≤ (√2 - 1) := by norm_num
        positivity
    -- then the angle is equal to (π / 8 + π / 2) + k * π
    · have angle_eq : π / 8 + ↑(2 * k + 1) * π / 2
        = ((π / 8 + π / 2) + k * π) := by
        push_cast
        ring
      -- unfold sinus and cosinus
      rw [angle_eq, Real.sin_add_int_mul_pi, Real.cos_add_int_mul_pi,
        Real.sin_add, Real.cos_add, Real.sin_pi_div_eight, Real.cos_pi_div_eight]
      -- the parity of k doesn't matter, we can simplify the equation to
      -- √(2 + √2) * (1 / 2) = √(2 - √2) * (3 / 2) + √(2 - √2) ^ 3 * (-1 / 2)
      suffices he : √(2 + √2) * (1 / 2) = √(2 - √2) * (3 / 2) + √(2 - √2) ^ 3 * (-1 / 2)
      · rcases Int.even_or_odd' k with ⟨k, rfl | rfl⟩
        -- when k is even
        · have k_even : Even (2 * k) := even_two_mul k
          have pow_eq_one : (-1 : ℝ) ^ (2 * k) = 1 := Even.neg_one_zpow k_even
          -- simplify
          norm_num [pow_eq_one]
          ring_nf
          exact he
        -- when k is odd
        · have k_odd : Odd (2 * k + 1) := odd_two_mul_add_one k
          have pow_eq_neg_one : (-1 : ℝ) ^ (2 * k + 1) = -1 := Odd.neg_one_zpow k_odd
          -- simplify
          rw [←neg_inj]
          norm_num [pow_eq_neg_one]
          ring_nf
          exact he

      -- simplify
      rw [sqrt_two_sub_sqrt_two_pow_three]

      -- square both sides
      rw [←sq_eq_sq₀]

      -- simplify
      ring_nf
      norm_num [sqrt_two_add_sqrt_two_sq, sqrt_two_sub_sqrt_two_sq]
      ring_nf
      norm_num
      ring_nf
      -- when squaring, we assumed both sides were positive
      · positivity
      · ring_nf
        positivity

/- Specific values of cosinus are equal to similar values of sinus.
   cos (π / 8 + k * π / 2) = sin (3 * (π / 8 + k * π / 2)) -/
lemma Real_cos_eq_sin_three_mul (k : ℤ)
  : Real.cos (π / 8 + k * π / 2) = Real.sin (3 * (π / 8 + k * π / 2)) := by
    -- remove angle multiples
    rw [Real.sin_three_mul]

    -- consider parity of k
    rcases Int.even_or_odd' k with ⟨k, rfl | rfl⟩
    -- then the angle is equal to π / 8 + k * π
    · have angle_eq : π / 8 + ↑(2 * k) * π / 2 = π / 8 + k * π := by
        push_cast
        ring

      -- unfold sinus and cosinus
      rw [angle_eq, Real.sin_add_int_mul_pi,
        Real.cos_add_int_mul_pi, Real.sin_pi_div_eight,
        Real.cos_pi_div_eight]

      -- the parity of k doesn't matter, we can simplify the equation to
      -- √(2 + √2) * (1 / 2) = √(2 - √2) * (3 / 2) + √(2 - √2) ^ 3 * (-1 / 2)
      suffices he : √(2 + √2) * (1 / 2) = √(2 - √2) * (3 / 2) + √(2 - √2) ^ 3 * (-1 / 2)
      · rcases Int.even_or_odd' k with ⟨k, rfl | rfl⟩
        -- when k is even
        · have k_even : Even (2 * k) := even_two_mul k
          have pow_eq_one : (-1 : ℝ) ^ (2 * k) = 1 := Even.neg_one_zpow k_even
          -- simplify
          norm_num [pow_eq_one]
          ring_nf
          exact he
        -- when k is odd
        · have k_odd : Odd (2 * k + 1) := odd_two_mul_add_one k
          have pow_eq_neg_one : (-1 : ℝ) ^ (2 * k + 1) = -1 := Odd.neg_one_zpow k_odd
          -- simplify
          rw [←neg_inj]
          norm_num [pow_eq_neg_one]
          ring_nf
          exact he

      -- simplify
      norm_num [sqrt_two_sub_sqrt_two_pow_three]

      -- square both sides
      rw [←sq_eq_sq₀]

      -- simplify
      ring_nf
      norm_num [sqrt_two_add_sqrt_two_sq, sqrt_two_sub_sqrt_two_sq]
      ring_nf
      norm_num
      ring
      -- when squaring, we assumed both sides were positive
      · positivity
      · ring_nf
        positivity
    -- then the angle is equal to (π / 8 + π / 2) + k * π
    · have angle_eq : π / 8 + ↑(2 * k + 1) * π / 2
        = (π / 8 + π / 2) + k * π := by
        push_cast
        ring
      -- unfold sinus and cosinus
      rw [angle_eq, Real.sin_add_int_mul_pi, Real.cos_add_int_mul_pi,
        Real.sin_add, Real.cos_add, Real.sin_pi_div_eight,
        Real.cos_pi_div_eight]
      -- the parity of k doesn't matter, we can simplify the equation to
      -- √(2 - √2) * (-1 / 2) = √(2 + √2) * (3 / 2) + √(2 + √2) ^ 3 * (-1 / 2)
      suffices he : √(2 - √2) * (-1 / 2) = √(2 + √2) * (3 / 2) + √(2 + √2) ^ 3 * (-1 / 2)
      · rcases Int.even_or_odd' k with ⟨k, rfl | rfl⟩
        -- when k is even
        · have k_even : Even (2 * k) := even_two_mul k
          have pow_eq_one : (-1 : ℝ) ^ (2 * k) = 1 := Even.neg_one_zpow k_even
          -- simplify
          norm_num [pow_eq_one]
          ring_nf
          exact he
        -- when k is odd
        · have k_odd : Odd (2 * k + 1) := odd_two_mul_add_one k
          have pow_eq_neg_one : (-1 : ℝ) ^ (2 * k + 1) = -1 := Odd.neg_one_zpow k_odd
          -- simplify
          rw [←neg_inj]
          norm_num [pow_eq_neg_one]
          ring_nf
          exact he

      -- simplify
      rw [sqrt_two_add_sqrt_two_pow_three, ←neg_inj]
      ring_nf

      -- square both sides
      rw [←sq_eq_sq₀]

      -- simplify
      ring_nf
      norm_num [sqrt_two_add_sqrt_two_sq, sqrt_two_sub_sqrt_two_sq]
      ring_nf
      norm_num
      ring_nf
      -- when squaring, we assumed both sides were positive
      · positivity
      · convert_to 0 ≤ √(2 + √2) * (√2 - 1) * (1 / 2)
        · ring_nf
        have sub_one_nonneg : 0 ≤ (√2 - 1) := by norm_num
        positivity


/- Specific values of cosinus are equal to the same value of sinus.
   sin (2 * (π / 8 + k * π / 2)) = cos (2 * (π / 8 + k * π / 2)) -/
lemma Real_sin_two_mul_eq_cos_two_mul (k : ℤ)
  : Real.sin (2 * (π / 8 + k * π / 2)) = Real.cos (2 * (π / 8 + k * π / 2)) := by
    have angle_eq : 2 * (π / 8 + ↑k * π / 2) = π / 4 + k * π := by ring
    rw [angle_eq, Real.sin_add_int_mul_pi, Real.cos_add_int_mul_pi]
    congr
    norm_num

/- Cosinus of 2 * π / 3 is -1 / 2. -/
lemma cos_two_mul_pi_div_three : cos (2 * (π / 3)) = -(1 / 2) := by
  rw [Real.cos_two_mul, Real.cos_pi_div_three]
  ring

/- If cosinus of a real number α is equal to -1 / 2, then α = 2 * k * π ± (2 * π / 3) for some integer k. -/
lemma cos_eq_neg_half {α : ℝ} (h : cos α = -(1 / 2))
  : ∃ (k : ℤ), α = k * (2 * Real.pi) + (2 * (π / 3)) ∨ α = k * (2 * Real.pi) - (2 * (π / 3)) := by
    rw [←cos_two_mul_pi_div_three] at h
    convert Real.cos_eq_cos_iff.mp h.symm using 3
    · ring_nf
    · ring_nf

/- Multisets of three elements are equal if they are reversals of each other. -/
lemma multiset_insert_three_eq (a b c : ℝ)
  : ({a, b, c} : Multiset ℝ) = {c, b, a} := by
    -- consider the multisets as lists
    convert_to ([a, b, c] : Multiset ℝ) = [c, b, a]

    -- the multisets are equal if the lists are permutations of each other
    simp only [Multiset.coe_eq_coe]

    -- but they are reversals of each other
    exact List.reverse_perm [c, b, a]


/- Agakhanov N.K.

Find all angles $\alpha$ for which the set of numbers $\sin \alpha, \sin 2 \alpha, \sin 3 \alpha$ coincides with the set $\cos \alpha, \cos 2 \alpha, \cos 3 \alpha$. -/
theorem algebra_219068 (α : ℝ) :
  ({Real.sin α, Real.sin (2 * α), Real.sin (3 * α)} : Multiset ℝ) =
  {Real.cos α, Real.cos (2 * α), Real.cos (3 * α)} ↔
  α ∈ {π / 8 + (k : ℝ) * π / 2 | k : ℤ} := by
    simp only [Set.mem_setOf_eq]
    constructor
    · intro eq
      -- we have that sin α + sin (2 * α) + sin (3 * α) = cos α + cos (2 * α) + cos (3 * α)
      have sum_eq : Multiset.sum {sin α, sin (2 * α), sin (3 * α)}
        = Multiset.sum {cos α, cos (2 * α), cos (3 * α)} := by
        rw [eq]
      norm_num at sum_eq

      -- use trig identities we find that
      -- sin (2 * α) * (1 + 2 * cos α) = cos (2 * α) * (1 + 2 * cos α)
      have sin_cos_eq : Real.sin (2 * α) * (1 + 2 * Real.cos α)
        = Real.cos (2 * α) * (1 + 2 * Real.cos α) := by
          -- we use the sum equality
          convert sum_eq using 1
          · have eqq : sin (2 * α) * (2 * cos α) = 2 * sin (2 * α) * cos α := by ring
            rw [mul_one_add, eqq, Real.two_mul_sin_mul_cos]
            ring_nf
          · have eqq : cos (2 * α) * (2 * cos α) = 2 * cos (2 * α) * cos α := by ring
            rw [mul_one_add, eqq, Real.two_mul_cos_mul_cos]
            ring_nf

      -- reorder to get a multiplication equal to zero
      -- (sin (2α) - cos (2α)) * (1 + 2cos α) = 0
      have eq_zero : (sin (2 * α) - cos (2 * α)) * (1 + 2 * cos α) = 0 := by linarith

      -- then one of the factors is zero
      rcases mul_eq_zero.mp eq_zero with h1 | h2
      -- if sin (2α) - cos (2α) = 0, then we have sin (2α) = cos (2α)
      · have eqq : sin (2 * α) = cos (2 * α) := sub_eq_zero.mp h1

        -- then we have 2 * α = 2 * k * π ± (π / 2 - 2 * α)
        rw [←Real.cos_pi_div_two_sub] at eqq
        rw [Real.cos_eq_cos_iff] at eqq

        -- check cases
        rcases eqq with ⟨k, h1 | h2⟩
        -- in positive case, then π / 8 + k * π / 2 = α, so we're done
        · ring_nf at h1
          have α_eq : α = (k * 4 + 1) / 8 * π := by linarith
          exists k
          convert α_eq.symm using 1
          · ring

        -- in negative case, we have that 2 * α = 2 * k * π - (π / 2 - 2 * α)
        · ring_nf at h2
          -- but that means 0 = (k - 1 / 4) * π
          have α_eq : 0 = (k - 1 / 4) * π := by linarith
          -- so one of the terms is zero
          rcases zero_eq_mul.mp α_eq with h3 | h4
          -- but k is an integer, so that case is impossible
          · have mul_eq : 4 * k = (1 : ℝ) := by linarith
            norm_cast at mul_eq
            omega
          -- and π is not zero, so that's impossible
          · have pi_ne : π ≠ 0 := pi_ne_zero
            contradiction
      -- if 1 + 2 * cos α = 0, cos α = -(1 / 2)
      · have cos_eq : cos α = -(1 / 2) := by linarith
        -- we have two solutions on the circle
        rcases cos_eq_neg_half cos_eq with ⟨k, h1 | h2⟩
        -- when α = k * (2 * π) + 2 * (π / 3) ...
        -- then 2 * α = 2 * (2 * (π / 3)) + (2 * k) * (2 * π)
        · have two_alpha : 2 * α = 2 * (2 * (π / 3)) + (2 * k : ℤ) * (2 * π) := by
            push_cast
            norm_num [h1]
            ring

          -- 3 * α = (3 * k + 1) * (2 * π)
          have three_alpha : 3 * α = (3 * k + 1 : ℤ) * (2 * π) := by
            push_cast
            norm_num [h1]
            ring

          -- cos (2 * α) = -(1 / 2)
          have cos_two : cos (2 * α) = -(1 / 2) := by
            rw [two_alpha, Real.cos_add_int_mul_two_pi, Real.cos_two_mul,
              Real.cos_two_mul, Real.cos_pi_div_three]
            norm_num

          -- cos (3 * α) = 1
          have cos_three : cos (3 * α) = 1 := by
            rw [three_alpha, Real.cos_int_mul_two_pi]

          -- sin (3 * α) = 0
          have sin_three : sin (3 * α) = 0 := by
            rw [three_alpha]
            convert_to sin (((3 * k + 1) * 2 : ℤ) * π) = 0
            · push_cast
              ring_nf
            rw [Real.sin_int_mul_pi]

          -- so the set contains 0
          have zero_mem : 0 ∈ ({sin α, sin (2 * α), sin (3 * α)} : Multiset ℝ) := by
            rw [sin_three]
            simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, or_true]

          -- but we know cos α, cos (2 * α), cos (3 * α) and none of them are 0
          have zero_not_mem : ¬0 ∈ ({sin α, sin (2 * α), sin (3 * α)} : Multiset ℝ) := by
            rw [eq, cos_eq, cos_two, cos_three]
            norm_num

          -- which is impossible
          contradiction
        -- when α = k * (2 * π) - 2 * (π / 3) ...
        -- then 2 * α = (2 * k) * (2 * π) - 2 * (2 * (π / 3))
        · have two_alpha : 2 * α = (2 * k : ℤ) * (2 * π) - 2 * (2 * (π / 3)) := by
            push_cast
            norm_num [h2]
            ring

          -- 3 * α = (3 * k - 1) * (2 * π)
          have three_alpha : 3 * α = (3 * k - 1 : ℤ) * (2 * π) := by
            push_cast
            norm_num [h2]
            ring

          -- then it's similar to the other case

          -- cos (2 * α) = -(1 / 2)
          have cos_two : cos (2 * α) = -(1 / 2) := by
            rw [two_alpha, Real.cos_int_mul_two_pi_sub, Real.cos_two_mul,
              Real.cos_two_mul, Real.cos_pi_div_three]
            norm_num

          -- cos (3 * α) = 1
          have cos_three : cos (3 * α) = 1 := by
            rw [three_alpha, Real.cos_int_mul_two_pi]

          -- sin (3 * α) = 0
          have sin_three : sin (3 * α) = 0 := by
            rw [three_alpha]
            convert_to sin (((3 * k - 1) * 2 : ℤ) * π) = 0
            · push_cast
              ring_nf
            rw [Real.sin_int_mul_pi]

          -- so the set contains 0
          have zero_mem : 0 ∈ ({sin α, sin (2 * α), sin (3 * α)} : Multiset ℝ) := by
            rw [sin_three]
            simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, or_true]

          -- but we know cos α, cos (2 * α), cos (3 * α) and none of them are 0
          have zero_not_mem : ¬0 ∈ ({sin α, sin (2 * α), sin (3 * α)} : Multiset ℝ) := by
            rw [eq, cos_eq, cos_two, cos_three]
            norm_num

          -- which is impossible
          contradiction

    -- we show that α = π / 8 + k * π / 2 is a valid solution
    · intro ⟨k, a_eq⟩
      rw [←a_eq]
      -- cos (3 * α) = sin α
      rw [←Real_sin_eq_cos_three_mul]
      -- sin (3 * α) = cos α
      rw [←Real_cos_eq_sin_three_mul]
      -- cos (2 * α) = sin (2 * α)
      rw [←Real_sin_two_mul_eq_cos_two_mul]

      -- so the sets are equal
      exact multiset_insert_three_eq _ _ _