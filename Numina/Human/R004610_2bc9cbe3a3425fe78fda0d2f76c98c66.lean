import Mathlib

open Real Set
open scoped BigOperators


-- first lemma is meant to remove that equaivalence of `Int.floor` and
-- replace it by membership to specific interval, bounded by integers

lemma lemma_1 (x y: ℝ) (Hx: x ≤ 0) (Hy: y ≤ 0):
    Int.floor x = Int.floor y ↔
    ∃ (k: ℕ), x ∈ Ico (- (k: ℝ)) (- (k: ℝ) + 1) ∧ y ∈ Ico (- (k: ℝ)) (- (k: ℝ) + 1) := by

  -- helpful tiny result
  have H (a: ℝ) (Ha: a ≤ 0): Int.floor a ≤ 0 := Int.floor_nonpos Ha

  constructor <;> intro H0
  . simp
    -- here we need to provide some integer that decides the interval.
    -- we use `⌊x⌋.natAbs`.
    -- later we will just use the fact that such integer exists
    use (Int.floor x).natAbs
    constructor
    . -- rewrite, simplify, apply the theorem
      rw [Int.cast_natAbs, abs_of_nonpos (H x Hx)]
      simp
      exact Int.floor_le x
    . -- same here
      rw [H0, Int.cast_natAbs, abs_of_nonpos (H y Hy)]
      simp
      exact Int.floor_le y
  . -- here we get the specific integer `k` and facts about it
    obtain ⟨k, H1, H2⟩ := H0
    -- simplify, prove some temporary results and rewrite with them
    simp at *
    have H3: Int.floor x = - k := Int.floor_eq_iff.mpr (by simp; exact H1)
    have H4: Int.floor y = - k := Int.floor_eq_iff.mpr (by simp; exact H2)
    rw [H3, H4]

-- another useful lemma for the proof
-- we go from the fact that `log x` belongs to the interval,
-- to the fact that `x` belong to the interval, determined by `exp` function

lemma lemma_2 (x: ℝ) (Hx1: 0 < x) (k: ℕ):
    log x ∈ Ico (- (k: ℝ) - 1) (- (k: ℝ)) ↔ x ∈ Ico (exp (- (k: ℝ) - 1)) (exp (- (k: ℝ))) := by
  -- proof is easy, thanks to the libary and use of `exact?`
  constructor <;> intros H
  . obtain ⟨H, H0⟩ := H
    constructor
    . exact (le_log_iff_exp_le Hx1).mp H
    . exact (log_lt_iff_lt_exp Hx1).mp H0
  . obtain ⟨H, H0⟩ := H
    constructor
    . exact (le_log_iff_exp_le Hx1).mpr H
    . exact (log_lt_iff_lt_exp Hx1).mpr H0

-- just a tiny lemma for purposes of simplification
-- it's use is to transform a nice set of `ℝ × ℝ` to even nicer one:
-- a product of two sets of `ℝ`

lemma lemma_3 (s1 s2: Set ℝ): {x: ℝ × ℝ | x.1 ∈ s1 ∧ x.2 ∈ s2 } = s1 ×ˢ s2 := by
  ext ⟨x, y⟩
  simp

-- for some reason, the direct rewrite in the proof didn't work.
-- that's the reason of such lemma

lemma lemma_4 (s1 s2: Set ℝ):
    MeasureTheory.volume (s1 ×ˢ s2) = MeasureTheory.volume s1 * MeasureTheory.volume s2 := by
  rw [<- MeasureTheory.Measure.prod_prod]
  rfl





/- 7. On a line segment $O A$ of length 1, two points $B$ and $C$ are chosen randomly. Let the length of segment $O B$ be $b$, and the length of segment $O C$ be $c$. Then the probability that $[\ln b]=[\ln c]$ is $\qquad$ -/
theorem calculus_289777 :
    (MeasureTheory.volume {p : ℝ × ℝ | p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 ∈ Icc 0 1 ∧ p.2 ∈ Icc 0 1 ∧ ⌊log p.1⌋ = ⌊log p.2⌋ }).toReal =
    (exp 1 - 1) / (exp 1 + 1) := by


  -- in the first step we modify the start set to something equal, but much nicer

  have step_1: { p: ℝ × ℝ | p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 ∈ Icc 0 1 ∧ p.2 ∈ Icc 0 1 ∧ ⌊log p.1⌋ = ⌊log p.2⌋} =
               { ((1: ℝ), (1: ℝ)) } ∪ { p: ℝ × ℝ | ∃ (k: ℕ),
                 p.1 ∈ Ico (exp (- (k: ℝ) - 1)) (exp (- (k: ℝ))) ∧
                 p.2 ∈ Ico (exp (- (k: ℝ) - 1)) (exp (- (k: ℝ))) } := by
    -- proof by extensionality
    ext ⟨x, y⟩
    constructor <;> intro H
    . -- direction from left to right
      -- we start by unpacking all the information in the hypothesis `H`
      obtain ⟨Hx, Hy, ⟨Hx0, Hx1⟩, ⟨Hy0, Hy1⟩, Hxy⟩ := H
      -- let's prove positivity of `x` and `y`
      have H1: 0 < x := lt_of_le_of_ne Hx0 (fun a => Hx a.symm)
      have H2: 0 < y := lt_of_le_of_ne Hy0 (fun a => Hy a.symm)
      -- first good rewrite using `lemma_1`
      rw [lemma_1 _ _ (log_nonpos Hx0 Hx1) (log_nonpos Hy0 Hy1)] at Hxy
      -- unpacking again
      obtain ⟨k, H3, H4⟩ := Hxy
      -- there are two cases to look at: `k = 0` and `0 < k`
      cases k with
      | zero =>
        -- we prove that in this case `x` and `y` are equal to one,
        -- in which case simple substitution works
        simp at *
        have H5: 1 ≤ x := (log_nonneg_iff H1).mp H3.1
        have H6: x = 1 := by linarith
        have H7: 1 ≤ y := (log_nonneg_iff H2).mp H4.1
        have H8: y = 1 := by linarith
        subst x y
        simp
      | succ k =>
        -- in the other case choose the right side option we use `k` as a witness element
        right
        use k
        -- useful rewrites with simplification everywhere
        rw [<- lemma_2 x H1, <- lemma_2 y H2]
        simp at *
        -- because `linarith` can't work with conjunctions in the goal,
        -- we destruct them manually and then use `linarith` on every goal this created
        constructor <;> constructor <;> linarith
    . -- direction from right to left
      simp at *
      -- again there are two cases - either singleton set, or a bigger one,
      -- that's the one we are interested in
      obtain ⟨x, y⟩ | ⟨k, ⟨Hx, Hy⟩⟩ := H
      . -- easy goal
        subst x y
        simp
      . -- first we create few lemmas for `linarith` to use and
        -- and solve almost all parts of the goal, except the last
        have H0 := exp_pos (- (k: ℝ) - 1)
        have H1: - (k: ℝ) ≤ 0 := by norm_cast; simp
        have Hx0: 0 < x := by linarith
        have Hx1: x ≤ 1 := by linarith [exp_le_exp.mpr H1, exp_zero]
        have Hy0: 0 < y := by linarith
        have Hy1: y ≤ 1 := by linarith [exp_le_exp.mpr H1, exp_zero]
        refine ⟨by linarith, by linarith, ⟨by linarith, Hx1⟩, ⟨by linarith, Hy1⟩, ?_⟩
        -- the last part of the goal
        -- thanks to `lemma_1` and `lemma`, we get something useful
        -- that is in end solved by tactic `linarith` again
        rw [lemma_1 _ _ (log_nonpos (le_of_lt Hx0) Hx1) (log_nonpos (le_of_lt Hy0) Hy1)]
        have H2 := lemma_2 x Hx0 k
        have H3 := lemma_2 y Hy0 k
        simp at H2 H3
        rw [<- H2] at Hx
        rw [<- H3] at Hy
        use (k + 1)
        simp
        constructor <;> constructor <;> linarith


  -- an very easy proof (thanks to simplification tactic), that
  -- the singleon set is disjoint from the other, bigger set
  have point_disjoint_with_the_set:
      Disjoint { ((1, 1): ℝ × ℝ) }
      { p: ℝ × ℝ | ∃ (k: ℕ),
      p.1 ∈ Ico (exp (- (k: ℝ) - 1)) (exp (- (k: ℝ))) ∧
      p.2 ∈ Ico (exp (- (k: ℝ) - 1)) (exp (- (k: ℝ))) } := by
    simp

  -- this singleton set is measurable
  have point_measurable: MeasurableSet { ((1, 1): ℝ × ℝ) } := by
    simp

  -- first important rewrite, basically the first step
  rw [step_1]

  -- the singleton set can be remoed, because it doesn't change
  -- the volume we want to calculate
  rw [MeasureTheory.measure_union' point_disjoint_with_the_set point_measurable]
  simp only [Prod.mk_one_one, MeasureTheory.measure_singleton, zero_add]

  -- we transform the set to indexed union of sets
  rw [setOf_exists]


  -- the proof that each two different sets in the indexed unio are disjoint
  have sets_pairwise_disjoint:
      Pairwise (Disjoint on fun (i: ℕ) => {(x: ℝ × ℝ) | x.1 ∈ Ico (exp (-(i: ℝ) - 1)) (exp (-(i: ℝ))) ∧
      x.2 ∈ Ico (exp (-(i: ℝ) - 1)) (exp (-(i: ℝ)))}) := by
    simp
    intros i j Hne s Hs1 Hs2
    simp at *
    ext x
    simp
    intro H
    have H1 := Hs1 H
    have H2 := Hs2 H
    simp at H1 H2
    obtain ⟨x, y⟩ := x
    have H3_i: - (i: ℝ) ≤ 0 := by norm_cast; simp
    have H3_j: - (j: ℝ) ≤ 0 := by norm_cast; simp
    have H4: 0 < x := by linarith [exp_pos (- (i: ℝ) - 1)]
    have H5: x ≤ 1 := by linarith [exp_le_exp.mpr H3_i, exp_zero]
    have H6: 0 < y := by linarith [exp_pos (- (i: ℝ) - 1)]
    have H7: y ≤ 1 := by linarith [exp_le_exp.mpr H3_j, exp_zero]
    -- after preparing a proving some useful stuff for the following use of lemmas,
    -- we can get to the main point.
    -- first we change parts of `H1` and `H2` to more useful form,
    -- touching only parts about `x`.
    -- that's will be enough to prove that `i` and `j` are equal
    -- (and get congradiction with `Hne` and with that solve the goal)
    have H8 := lemma_2 x H4 i
    have H9 := lemma_2 x H4 j
    simp at H8 H9 H1 H2
    rw [<- H8] at H1
    rw [<- H9] at H2
    -- we prove that `log x + 1` is simultatneously `- i` and `- j`,
    -- therefore `i = j`
    have H8: Int.floor (log x + 1) = (- (i: ℤ)) := by
      rw [Int.floor_eq_iff]
      simp
      constructor <;> linarith
    have H9: Int.floor (log x + 1) = (- (j: ℤ)) := by
      rw [Int.floor_eq_iff]
      simp
      constructor <;> linarith
    have H10: i = j := by
      rw [H8] at H9
      simp at H9
      exact H9
    itauto

  -- also we prove that all the indexed union are measurable
  -- as the set is product of two simpler sets, we use that
  -- and the fact that simple intervals are measurable
  have sets_are_measurable:
      ∀ (i: ℕ), MeasurableSet { (x: ℝ × ℝ) | x.1 ∈ Ico (exp (-(i: ℝ) - 1)) (exp (-(i: ℝ))) ∧
       x.2 ∈ Ico (exp (-(i: ℝ) - 1)) (exp (-(i: ℝ))) } := by
    intros i
    apply MeasurableSet.prod
    . apply measurableSet_Ico
    . apply measurableSet_Ico

  -- with these conditionbs proven, we can change the volume of
  -- the indexed uniton to sum over all natural numbres of these individual sets
  rw [MeasureTheory.measure_iUnion sets_pairwise_disjoint sets_are_measurable]

  -- some more rewrites to even more simplify the expression in the goal
  -- as each individual set is the product of teo intervals,
  -- then the volumes of these sets is equal to product
  -- of the interval lengths
  simp_rw [lemma_3, lemma_4, volume_Ico]

  -- now some calculations/manipulations to simplify the expression in the goal
  have some_calculations (i: ℕ):
      ENNReal.ofReal ((exp (-(i: ℝ)) - exp (-(i: ℝ) - 1))) * ENNReal.ofReal ((exp (-(i: ℝ)) - exp (-(i: ℝ) - 1))) =
      ENNReal.ofReal ((exp 1 - 1) ^ (2: ℕ) / exp 2 * (exp (- 2)) ^ i) := by
    rw [<- ENNReal.ofReal_mul]
    . congr 1
      have H := exp_ne_zero 2
      rw [<- sq]
      field_simp
      have H0: exp 2 = exp 1 ^ (2: ℕ) := by simp only [exp_one_pow, Nat.cast_ofNat]
      rw [H0]
      have H1: exp (- 2) ^ i = (exp (- (i: ℝ))) ^ (2: ℕ) := by
        rw [sq, <- exp_add]
        rw [<- Real.rpow_natCast]
        rw [<- exp_mul]
        congr
        ring
      rw [H1]
      rw [<- mul_pow, <- mul_pow]
      congr 1
      rw [sub_mul]
      nth_rw 2 [<- exp_add]
      ring_nf
    . simp

  -- now, after this rewrite, goal looks better
  simp_rw [some_calculations]

  -- one lemma, that will be useful for moving that `ENNReal.ofReal` outside the sum sign
  -- each summand is nonnegative
  have each_summand_nonneg (i: ℕ): 0 ≤ (exp 1 - 1) ^ (2: ℕ) / exp 2 * exp (-2) ^ i := by
    rw [<- Real.rpow_natCast]
    have H := exp_nonneg 2
    have H0: 0 ≤ (exp 1 - 1) ^ (2: ℕ) := sq_nonneg (exp 1 - 1)
    have H1: 0 ≤ exp (-2) ^ i := by
      apply Nonneg.pow_nonneg
      apply exp_nonneg
    have H2: 0 ≤ (exp 1 - 1) ^ (2: ℕ) / exp 2 := div_nonneg H0 H
    simp
    exact mul_nonneg H2 H1

  -- quotient of the geometric sequence, hidden under the sum sign,
  -- is less than 1
  have quotient_lt_one: exp (- 2) < 1 := by
    have H: - 2 < (0: ℝ) := by simp
    linarith [exp_lt_exp.mpr H, exp_zero]

  -- and also nonnegative
  have quotient_nonneg: 0 ≤ exp (- 2) := by
    exact exp_nonneg (- 2)

  -- now we use those results to prove that geometric sequence is summable
  have function_is_summable: Summable (fun (i: ℕ) => exp (-2) ^ i) := by
    apply summable_geometric_of_lt_one
    . exact quotient_nonneg
    . exact quotient_lt_one

  -- the expression that the geometric sequence is multipled by, is nonzero
  have multiplier_is_nonzero: (exp 1 - 1) ^ (2: ℕ) / exp 2 ≠ 0 := by
    intro H
    simp at H
    rw [sub_eq_zero] at H
    linarith [(exp_eq_one_iff 1).mp H]


  -- further rewrites, although we still have that `ENNReal.ofReal` and `toReal` to remove
  rw [<- ENNReal.ofReal_tsum_of_nonneg each_summand_nonneg
    ((summable_mul_left_iff multiplier_is_nonzero).mpr function_is_summable)]
  rw [Summable.tsum_mul_left ((exp 1 - 1) ^ (2: ℕ) / exp 2) function_is_summable]
  rw [tsum_geometric_of_lt_one quotient_nonneg quotient_lt_one]

  -- for that purpose let's prove that this expression is nonnegative
  have expression_nonnegative: 0 ≤ (exp 1 - 1) ^ 2 / exp 2 * (1 - exp (-2))⁻¹ := by
    have H := exp_nonneg 2
    have H0: 0 ≤ (exp 1 - 1) ^ (2: ℕ) := sq_nonneg (exp 1 - 1)
    have H1: exp (-2) < 1 := by
      rw [exp_lt_one_iff]
      norm_num
    have H2: 0 ≤ (exp 1 - 1) ^ (2: ℕ) / exp 2 := by exact div_nonneg H0 H
    have H3: 0 < 1 - exp (-2) := sub_pos.mpr quotient_lt_one
    have H4: 0 < (1 - exp (- 2))⁻¹ := inv_pos_of_pos H3
    exact (mul_nonneg_iff_of_pos_right H4).mpr H2

  -- finally no more `ENNReal.toReal` :)
  rw [ENNReal.toReal_ofReal expression_nonnegative]

  -- three statements about being nonzero values, which
  -- will be useful for `field_simp` tactic
  have nonzero_1: exp 2 ≠ 0 := exp_ne_zero 2
  have nonzero_2: 1 - exp (- 2) ≠ 0 := by
    intro H
    rw [sub_eq_zero] at H
    symm at H
    rw [exp_eq_one_iff] at H
    norm_num at H
  have nonzero_3: exp 1 + 1 ≠ 0 := by
    linarith [exp_pos 1]

  -- now the last step - just have to prove equality
  field_simp
  rw [sq]
  rw [mul_assoc]
  congr 1
  ring_nf
  rw [sq]
  rw [<- exp_add, <- exp_add]
  norm_num
  ring