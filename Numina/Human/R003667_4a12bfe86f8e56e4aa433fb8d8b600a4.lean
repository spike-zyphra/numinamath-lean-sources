import Mathlib

set_option maxHeartbeats 400000

open Real Set
open scoped BigOperators

-- just a lemma for rewriting absolute values of real numbers
-- with expressions with `if...then...else`
lemma abs_to_if (x: ℝ): abs x = if x < 0 then - x else x := by
    split_ifs <;> rename_i H
    . rw [abs_of_neg H]
    . rw [abs_of_nonneg (by linarith)]

-- helper lemma:
-- if every two sets with different numbers are disjoint, then
-- the union of first `n` sets and `n + 1`-th set are disjoint
lemma about_disjointness_of_iUnion {A} (n: ℕ) (s: ℕ → Set A) (H: ∀ i j, i ≠ j → Disjoint (s i) (s j)):
    Disjoint (⋃ (k ∈ Set.Ico (0: ℕ) n), s k) (s n) := by
  induction n with
  | zero => simp
  | succ n iH =>
    simp only [Set.mem_Ico, zero_le, true_and, Set.disjoint_iUnion_left]
    intros i Hi
    apply H
    omega

-- if all sets are finite, then union of finite number of them is finite too
lemma iUnion_of_finite_sets_is_finite {A} (n: ℕ) (s: ℕ → Set A) (H: ∀ i, (s i).Finite):
    (⋃ (k ∈ Set.Ico (0: ℕ) n), s k).Finite := by
  induction n with
  | zero => simp
  | succ n iH =>
    simp only [Set.mem_Ico, zero_le, true_and] at *
    rw [Set.biUnion_lt_succ, Set.finite_union]
    exact ⟨iH, H n⟩

-- if we know that every two sets with different numbers are disjoint
-- and also every set is finite, then we have nice formula for cardinality of the finite union:
-- it is equal to sum of sum of cardinalities of first `n` sets
lemma ncard_of_iUnion_of_disjoint_finite_sets_as_sum_aux
    {A} (n: ℕ) (s: ℕ → Set A) (H: ∀ i j, i ≠ j → Disjoint (s i) (s j)) (H0: ∀ i, Finite (s i)):
    (⋃ (i ∈ Set.Ico (0: ℕ) n), (s i)).ncard = ∑ (i ∈ Set.Ico (0: ℕ) n), (s i).ncard := by
  induction n with
  | zero => simp
  | succ n iH =>
    simp at *
    rw [Set.biUnion_lt_succ, Set.ncard_union_eq]
    . rw [Finset.sum_range_succ]
      congr
    . have H := about_disjointness_of_iUnion n s H
      simp at *
      exact H

-- almost the same as the previous set, but with changed conditions.
-- this time we know that two sets are disjoint, if their numbers are less than some limit,
-- and also the set is known to be finite only if its number is less than the limit.
lemma ncard_of_iUnion_of_disjoint_finite_sets_as_sum
    {A} (limit: ℕ) (s: ℕ → Set A) (H: ∀ i j, i < limit → j < limit → i ≠ j → Disjoint (s i) (s j))
    (H0: ∀ i, i < limit → Finite (s i)):
    (⋃ (i ∈ Set.Ico (0: ℕ) limit), (s i)).ncard = ∑ (i ∈ Set.Ico (0: ℕ) limit), (s i).ncard := by
  -- we define special function that's gives empty set on all unallowed values,
  -- prove necessary properties for application of the previous lemma,
  -- afterwards we do some more work on this result and get what we needed
  set s': ℕ → Set A := fun i => if i < limit then s i else ∅
  -- the fact about disjointness
  have s'_disjoint i j (Hne: i ≠ j): Disjoint (s' i) (s' j) := by
    unfold s'
    split_ifs <;> rename_i H1 H2
    . exact H i j H1 H2 Hne
    . simp
    . simp
    . simp
  -- the fact about finiteness
  have s'_finite i: (s' i).Finite := by
    unfold s'
    split_ifs <;> rename_i H1
    . exact H0 i H1
    . simp
  -- now we get this result, that must be transformed a bit to solve the goal
  have H1 := ncard_of_iUnion_of_disjoint_finite_sets_as_sum_aux limit s' s'_disjoint s'_finite
  unfold s' at H1
  rw [Set.biUnion_eq_iUnion] at H1
  rw [Set.iUnion_ite] at H1
  simp at H1
  have H2 (x: ℕ): (if x < limit then s x else ∅).ncard = (if x < limit then (s x).ncard else 0) := by
    split_ifs <;> rename_i H2
    . rfl
    . simp
  simp_rw [H2] at H1
  simp at *
  rw [Finset.sum_ite_of_true] at H1
  . rw [<- H1]
    congr
    ext i
    simp
  . simp


/- 19. For $0 \leq x \leq 1$ and positive integer $n$, let $f_{0}(x)=|1-2 x|$ and $f_{n}(x)=f_{0}\left(f_{n-1}(x)\right)$. How many solutions are there to the equation $f_{10}(x)=x$ in the range $0 \leq x \leq 1$ ?
對於 $0 \leq x \leq 1$ 和正整數 $n$, 設 $f_{0}(x)=|1-2 x|$ 和 $f_{n}(x)=f_{0}\left(f_{n-1}(x)\right)$ 。那麼方程 $f_{10}(x)=x$ 在 $0 \leq x \leq 1$ 區間內有多少個解? -/
theorem algebra_205591 (f : ℕ → ℝ → ℝ)
    (h₀ : ∀ x, f 0 x = abs (1 - 2 * x))
    (h₁ : ∀ n x, f (n + 1) x = f 0 (f n x)) :
    {x | 0 ≤ x ∧ x ≤ 1 ∧ f 10 x = x}.ncard = 2048 := by

  -- these lemmas will remain inside the proof, because they use
  -- all these hypotheses about the problem and
  -- and they are kind of relevant to the problem

  -- the first lemma is about the value of the function `f` for any `n`,
  -- if the parameter `t` is in the interval `[0, 1 / 2 ^ n]`:
  -- in such case `f n t = abs (1 - 2 ^ (n + 1) * t)`

  -- the proof is by induction on parameter `n`.
  -- if `n` is zero, then proof is very simple
  -- if we do the induction step, have induction hypothesis `iH`
  -- and want to prove the result for `n + 1`, then
  -- there is some work, but not much
  have aux_lemma_1 (n: ℕ) (t: ℝ) (Ht0: 0 ≤ t) (Ht1: 2 ^ n * t ≤ 1):
      f n t = abs ((1: ℝ) - 2 ^ (n + 1) * t) := by
    induction n with
    | zero =>
      rw [h₀]
      simp
    | succ n iH =>
      -- rewrite in the goal using the given hypotheses about the function:
      -- first some rewrites using `h₁` and `h₀
      rw [h₁, h₀]
      -- the induction hypothesis uses the fact `2 ^ n * t ≤ 1`,
      -- so we will need to prove it.
      -- the proof is simple: rewrite, simplify, `linarith`
      have H0: 2 ^ n * t ≤ 1 := by
        rw [pow_add] at Ht1
        simp at Ht1
        linarith
      -- then we rewrite in the goal, using the induction hypothesis with
      -- this necessary parameter/input `H0`
      rw [iH H0]
      -- now change the absolute value function with the specified parameter
      -- to the expression with `if`, and then we split this `if`
      rw [abs_to_if (1 - 2 ^ (n + 1) * t)]
      split_ifs <;> rename_i H1
      . -- easy proof
        ring_nf
        linarith
      . -- a tiny bit more advanced proof: first tactic `ring_nf` to simplify,
        -- then we show that the expression under the absolute value signs
        -- (or given as parameters to `abs` function) are
        -- direct opposites of each other.
        -- and this is exactly the case that library lemma `abs_neg`
        -- takes care of
        ring_nf
        rw [show -1 + t * 2 ^ n * 4 = - (1 - t * 2 ^ n * 4) by ring]
        apply abs_neg

  -- the second lemma is about the fact that the function for any given `n`
  -- is symmetrical in the interval `[0, 1]`

  -- there we do the induction on `n` again and the proof is comfortably short
  have aux_lemma_2 (n: ℕ): ∀ t, f n t = f n (1 - t) := by
    induction n with
    | zero =>
      intro t
      -- some rewrites in the goal using the properties oft he function `f`,
      -- then simplifications and again proof by the library lemma `abs_neg`
      rw [h₀, h₀]
      ring_nf
      rw [show -1 + t * 2 = - (1 - t * 2) by ring]
      rw [abs_neg]
    | succ n iH =>
      -- surprisingly the induction step's proof is even shorter:
      -- just five rewrites
      intro t
      rw [h₁, h₁, h₀, h₀, iH]

  -- the third lemma is about the fact that in the interval `[0, 1/2]`
  -- and for each natural `n` the function `f (n + 1)` looks like
  -- compressed (scaled) function `f n` in the all interval `[0, 1]`

  -- no big suprises here, we do again the induction on variable `n`
  have aux_lemma_3 (n: ℕ): ∀ t, t ∈ Icc 0 (1 / 2) → f (n + 1) t = f n (2 * t) := by
    induction n with
    | zero =>
      -- simplications, rewrites, in the end splitting of many `if`s
      -- created by the lemma `abs_to_if` and the tactic `linarith`
      -- solves all the goals
      intros t Ht
      simp at Ht
      rw [h₁, h₀, h₀, h₀]
      rw [abs_to_if, abs_to_if, abs_to_if]
      split_ifs <;> rename_i H H0 H1 <;> linarith
    | succ n iH =>
      -- again the induction step part is surprisingly short
      intros t Ht
      rw [h₁, h₀, iH t Ht, h₁, h₀]

  -- this lemma is about the scaling and also some translation:
  -- if the argument `t` is in interval `[1 / 2, 1]`,
  -- then there is formula for `f (n + 1) t`
  have aux_lemma_4 (n: ℕ): ∀ t, t ∈ Icc (1 / 2) 1 → f (n + 1) t = f n (2 * t - 1) := by
    induction n with
    | zero =>
      intros t Ht
      simp at Ht ⊢
      rw [h₁, h₀, h₀, h₀]
      rw [abs_to_if, abs_to_if, abs_to_if]
      split_ifs <;> rename_i H H0 H1 <;> linarith
    | succ n iH =>
      intros t Ht
      rw [h₁, h₀, iH t Ht, h₁, h₀]


  -- now the following lemma is about the specific formula for
  -- the function `f` in each of the `2 ^ n` segments `[i / 2 ^ n , (i + 1) / 2 ^ n]`
  -- here the proof will be much messier than with
  -- three previous lemmas, because, well, as you can see -
  -- this lemma is much more complex

  -- we start with induction on `n`
  have formula (n: ℕ):
      ∀ (t: ℝ) (i: ℕ) (hi: i < 2 ^ n),
      t * 2 ^ n ∈ Icc (i: ℝ) ((i: ℝ) + 1) →
      f n t = abs ((1: ℝ) + 2 * i - 2 * 2 ^ n * t) := by
    induction n with
    | zero =>
      -- this part is easy
      intros t i Hi Ht
      simp at *
      subst i
      simp
      rw [h₀]
    | succ n iH =>
      intros t i Hi Ht

      -- now let's prove that `0 ≤ t` - that it follows
      -- from the hypotheses of this lemma
      -- (lots of awful looking lemma uses etc.)
      have H: 0 ≤ t := by
        obtain ⟨Ht1, Ht2⟩ := Ht
        have H0: 0 ≤ (i: ℝ) := Nat.cast_nonneg' i
        have H1: 0 < (2: ℝ) ^ (n + 1) := by norm_cast; exact Nat.two_pow_pos (n + 1)
        have H2: 0 < 1 / (2: ℝ) ^ (n + 1) := one_div_pos.mpr H1
        have H3: 0 ≤ (i: ℝ) * (1 / (2: ℝ) ^ (n + 1)) := (mul_nonneg_iff_of_pos_right H2).mpr H0
        have H4: (i: ℝ) / 2 ^ (n + 1) ≤ t := (div_le_iff₀ H1).mpr Ht1
        field_simp at H3
        linarith

      -- let's prove also that `t ≤ 1`
      -- (again a mess, sadly)
      have H0: t ≤ 1 := by
        obtain ⟨Ht1, Ht2⟩ := Ht
        have H0: 0 < (2: ℝ) ^ (n + 1) := by norm_cast; exact Nat.two_pow_pos (n + 1)
        have H1: t ≤ ((i: ℝ) + 1) / (2 ^ (n + 1)) := (le_div_iff₀ H0).mpr Ht2
        have H2: ((i: ℝ) + 1) ≤ (2: ℝ) ^ (n + 1) := by norm_cast
        have H3: ((i: ℝ) + 1) / (2: ℝ) ^ (n + 1) ≤ 1 := (div_le_one₀ H0).mpr H2
        linarith

      -- now we will prove that there are three possible cases:
      -- 1) `0 ≤ t < 1 / 2`
      -- 2) `t = 1 / 2`
      -- 3) `1 / 2 < t ≤ 1`
      have H1: t ∈ Ico 0 (1 / 2) ∨ t = 1 / 2 ∨ t ∈ Ioc (1 / 2) 1 := by
        -- first some simplification
        simp
        field_simp
        -- then the use of lemma `lt_trichotmy` with simple proofs in each case
        obtain H2 | H2 | H2 := lt_trichotomy t (1 / 2)
        . tauto
        . subst t
          simp
        . tauto

      -- now we consider each of these three cases
      obtain H1 | H1 | H1 := H1

      . -- case where `t` is in the interval `[0, 1 / 2)`
        -- at first we use the third lemma we proved previously
        -- on the goal
        rw [aux_lemma_3 n _ (mem_Icc_of_Ico H1)]
        -- simplifications
        rw [pow_add]
        simp
        -- rewrite necessary for the successful application of
        -- the induction hypothesis `iH` on the goal
        rw [show 2 * ((2: ℝ) ^ n * 2) * t = 2 * (2: ℝ) ^ n * (2 * t) by ring]
        -- finally an rewrite using induction hypothesis with
        -- specific parameter value
        rw [<- iH (2 * t)]
        . -- induction hypothesis needed additional facts that
          -- we will now prove (again the proof will be messy, sadly)
          -- the first fact is that `i < 2 ^ n`
          obtain ⟨Ht1, Ht2⟩ := Ht
          obtain ⟨H1, H2⟩ := H1
          have H3: 0 < (2: ℝ) ^ (n + 1) := by norm_cast; exact Nat.two_pow_pos (n + 1)
          have H4: t * (2: ℝ) ^ (n + 1) < (1: ℝ) / 2 * (2: ℝ) ^ (n + 1) :=
            (mul_lt_mul_iff_of_pos_right H3).mpr H2
          nth_rw 2 [pow_add] at H4
          field_simp at H4
          have H5: (i: ℝ) < 2 ^ n := lt_of_le_of_lt Ht1 H4
          norm_cast at H5
        . -- the second fact is more specific, but actually easy to prove
          rw [show t * (2: ℝ) ^ (n + 1) = 2 * t * (2: ℝ) ^ n by ring] at Ht
          exact Ht

      . -- the case where `t` is exactly equal to `1 / 2`
        rw [H1, aux_lemma_3 n _ (by subst t; simp)]
        simp
        rw [aux_lemma_2]
        simp
        rw [aux_lemma_1 n 0 (by simp) (by simp)]
        simp
        field_simp
        rw [H1] at Ht
        field_simp at Ht
        rw [pow_add] at Ht
        field_simp at Ht
        norm_cast at Ht

        -- now we have two possible values for variable `i`.
        -- in each of the cases the goal can be proven
        have H2: i = 2 ^ n - 1 ∨ i = 2 ^ n := by omega
        obtain H2 | H2 := H2
        . subst i
          simp
          ring_nf
          simp
        . subst i
          simp
          ring_nf
          simp

      . -- the case where `t` is in interval `(1 / 2, 1]`.
        -- first we rewrite the left side of the goal to

        -- let's change the `f (n + 1) t` to `f n (2 * t - 1)` by a rewrite
        rw [aux_lemma_4 n t (mem_Icc_of_Ioc H1)]

        -- following result (`H3`) will be useful for a few rewrites
        have H2: 2 ^ n ≤ i := by
          obtain ⟨Ht1, Ht2⟩ := Ht
          obtain ⟨H1, H2⟩ := H1
          rw [pow_add] at *
          simp at Hi Ht1 Ht2
          have H3: (1: ℝ) / 2 * (2 ^ n * 2) < (i: ℝ) + 1 := by
            nlinarith
          field_simp at H3
          norm_cast at H3
          omega

        have H3: @Nat.cast ℝ instNatCast (i - 2 ^ n) = (i: ℝ) - (2: ℝ) ^ n := by norm_cast

        -- now we apply induction hypothesis with specific arguments
        rw [iH (2 * t - 1) (i - 2 ^ n)]
        . -- easy
          rw [H3]
          ring_nf
        . -- also easy, thanks to `omega`
          rw [pow_add] at Hi
          omega
        . -- this is a bit more difficult:
          -- to prove that the number is in specific interval
          constructor
          . rw [H3]
            field_simp
            ring_nf
            obtain ⟨Ht1, Ht2⟩ := Ht
            rw [pow_add] at Ht1
            linarith
          . rw [H3]
            ring_nf
            field_simp
            ring_nf
            obtain ⟨Ht1, Ht2⟩ := Ht
            rw [pow_add] at Ht2
            linarith

  -- just useful abbreviation
  set tiny_interval: ∀ (n i: ℕ), Set ℝ := fun n i => Ioc ((i: ℝ) / 2 ^ n) (((i: ℝ) + 1) / 2 ^ n)

  -- number of roots in each tiny interval is exactly 2
  have number_of_roots_in_each_interval (n i: ℕ) (Hi: i < 2 ^ n):
      { x | x ∈ tiny_interval n i ∧ f n x = x }.ncard = 2 := by
    unfold tiny_interval
    rw [ncard_eq_two]

    -- we use this explicit formula for values of both roots
    use (1 + 2 * (i: ℝ)) / (2 * (2: ℝ) ^ n + 1), (1 + 2 * (i: ℝ)) / (2 * (2: ℝ) ^ n - 1)

    have H: 2 * (2: ℝ) ^ n + 1 ≠ 0 := by
      norm_cast
    have H0: 2 * (2: ℝ) ^ n - 1 ≠ 0 := by
      intro H1
      rw [sub_eq_zero] at H1
      norm_cast at H1
      simp at H1

    constructor
    . -- we need to prove that both roots are in fact different numbers
      field_simp
      constructor
      . intro H1
        linarith
      . intro H1
        norm_cast at H1
        simp at H1
    . -- now we have to prove that two sets are in fact equal:
      -- the first is the set of all solutions in the specific interval,
      -- the second is the set of the two explicit solutions
      ext x
      simp

      -- useful fact later
      have H3: 0 < (2: ℝ) ^ n := by
        norm_cast
        exact Nat.two_pow_pos n

      constructor <;> intro H1
      . -- the first direction: we prove that all values that are solutions in the specific "tiny" interval,
        -- are actually one of two possible values
        obtain ⟨H1, H2⟩ := H1
        rw [formula n x i Hi] at H2
        . rw [abs_to_if] at H2
          split_ifs at H2; rename_i H3
          . right
            field_simp
            linarith
          . left
            field_simp
            linarith
        . obtain ⟨H4, H5⟩ := H1
          constructor
          . have H6: (i: ℝ) / (2: ℝ) ^ n * 2 ^ n ≤ x * 2 ^ n :=
              (mul_le_mul_iff_of_pos_right H3).mpr (le_of_lt H4)
            field_simp at H6
            exact H6
          . have H6: x * (2: ℝ) ^ n ≤ ((i: ℝ) + 1) / 2 ^ n * 2 ^ n :=
              (mul_le_mul_iff_of_pos_right H3).mpr H5
            field_simp at H6
            exact H6
      . -- the second direction: we prove that both these explicit solutions are actual roots
        -- in the corresponding tiny interval
        have H4: (2: ℝ) ^ n ≠ 0 := by
          norm_cast
          exact Nat.not_eq_zero_of_lt Hi
        have H5: 0 < 2 * (2: ℝ) ^ n + 1 := by
          norm_cast
          omega
        have H6: 0 < 2 * (2: ℝ) ^ n - 1 := by
          have H7: 1 < 2 ^ (n + 1) := Nat.one_lt_two_pow' n
          have H8: (1: ℝ) < (2: ℝ) ^ (n + 1) := by
            norm_cast
          rw [pow_add] at H8
          linarith
        refine ⟨⟨?_, ?_⟩, ?_⟩
        . obtain H1 | H1 := H1
          . subst x
            have H7: (i: ℝ) * (2 * (2: ℝ) ^ n + 1) < (1 + 2 * (i: ℝ)) * ((2: ℝ) ^ n) := by
              ring_nf
              rw [add_comm]
              field_simp
              norm_cast
            have H8: (i: ℝ) < (1 + 2 * (i: ℝ)) * (2: ℝ) ^ n / (2 * (2: ℝ) ^ n + 1) :=
              by exact (lt_div_iff₀ H5).mpr H7
            rw [mul_div_right_comm] at H8
            exact (div_lt_div_iff₀ H3 H5).mpr H7
          . subst x
            have H7: (i: ℝ) * (2 * (2: ℝ) ^ n - 1) < (1 + 2 * (i: ℝ)) * ((2: ℝ) ^ n) := by
              ring_nf
              rw [add_comm]
              field_simp
              norm_cast
              omega
            have H8: (i: ℝ) < (1 + 2 * (i: ℝ)) * (2: ℝ) ^ n / (2 * (2: ℝ) ^ n - 1) :=
              (lt_div_iff₀ H6).mpr H7
            rw [mul_div_right_comm] at H8
            exact (div_lt_div_iff₀ H3 H6).mpr H7
        . obtain H1 | H1 := H1
          . subst x
            have H7: (1 + 2 * (i: ℝ)) * (2: ℝ) ^ n ≤ ((i: ℝ) + 1) * (2 * (2: ℝ) ^ n + 1) := by
              ring_nf
              norm_cast
              omega
            have H8: (1 + 2 * (i: ℝ)) ≤ ((i: ℝ) + 1) * (2 * (2: ℝ) ^ n + 1) / (2: ℝ) ^ n :=
              (le_div_iff₀ H3).mpr H7
            rw [mul_div_right_comm] at H8
            exact (div_le_div_iff₀ H5 H3).mpr H7
          . subst x
            have H7: (1 + 2 * (i: ℝ)) * (2: ℝ) ^ n ≤ ((i: ℝ) + 1) * (2 * (2: ℝ) ^ n - 1) := by
              ring_nf
              have H8: (1 + (i: ℝ)) + ((i: ℝ) * (2: ℝ) ^ n * 2 + 2 ^ n) ≤
                       (1 + (i: ℝ)) + (-1 - (i: ℝ) + (i: ℝ) * 2 ^ n * 2 + 2 ^ n * 2) := by
                ring_nf
                norm_cast
                omega
              exact (add_le_add_iff_left (1 + (i: ℝ))).mp H8
            have H8: (1 + 2 * (i: ℝ)) ≤ ((i: ℝ) + 1) * (2 * (2: ℝ) ^ n - 1) / (2: ℝ) ^ n :=
              (le_div_iff₀ H3).mpr H7
            rw [mul_div_right_comm] at H8
            exact (div_le_div_iff₀ H6 H3).mpr H7
        . rw [formula n x i Hi]
          . obtain H1 | H1 := H1
            . subst x
              rw [abs_of_pos]
              . field_simp
                ring_nf
              . field_simp
                ring_nf
                field_simp
                norm_cast
                omega
            . subst x
              rw [abs_of_neg]
              . field_simp
                ring_nf
              . field_simp
                ring_nf
                field_simp
                have H7: -((i: ℝ) * 2) < 1 := by
                  have H7: 0 < 1 + (i: ℝ) * 2 := by
                    norm_cast
                    omega
                  exact neg_lt_iff_pos_add.mpr H7
                ring_nf at H6
                exact (div_lt_div_iff_of_pos_right H6).mpr H7
          . obtain H1 | H1 := H1
            . subst x
              constructor
              . field_simp
                have H7: (i: ℝ) * (2 * (2: ℝ) ^ n + 1) ≤ (1 + 2 * (i: ℝ)) * 2 ^ n := by
                  ring_nf
                  norm_cast
                  omega
                exact (le_div_iff₀ H5).mpr H7
              . field_simp
                have H7: (1 + 2 * (i: ℝ)) * (2: ℝ) ^ n ≤ ((i: ℝ) + 1) * (2 * (2: ℝ) ^ n + 1) := by
                  ring_nf
                  norm_cast
                  omega
                exact (div_le_iff₀ H5).mpr H7
            . constructor
              . subst x
                field_simp
                have H7: (i: ℝ) * (2 * (2: ℝ) ^ n - 1) ≤ (1 + 2 * (i: ℝ)) * (2: ℝ) ^ n := by
                  ring_nf
                  have H8: (i: ℝ) + (-(i: ℝ) + (i: ℝ) * (2: ℝ) ^ n * 2) ≤ (i: ℝ) + ((i: ℝ) * (2: ℝ) ^ n * 2 + (2: ℝ) ^ n) := by
                    ring_nf
                    norm_cast
                    omega
                  linarith
                exact (le_div_iff₀ H6).mpr H7
              . subst x
                field_simp
                have H7: (1 + 2 * (i: ℝ)) * (2: ℝ) ^ n ≤ ((i: ℝ) + 1) * (2 * 2 ^ n - 1) := by
                  ring_nf
                  have H8: (1 + (i: ℝ)) + ((i: ℝ) * (2: ℝ) ^ n * 2 + (2: ℝ) ^ n) ≤
                           (1 + (i: ℝ)) + (-1 - (i: ℝ) + (i: ℝ) * (2: ℝ) ^ n * 2 + (2: ℝ) ^ n * 2) := by
                    ring_nf
                    norm_cast
                    omega
                  linarith
                exact (div_le_iff₀ H6).mpr H7

  -- here we express the interval `[0, 1]` as an union of singleton set with value `0` and
  -- indexed set which is basically made of lots of tiny intervals
  have interval_zero_to_one_as_union n:
      Icc 0 1 = {0} ∪ (⋃ i ∈ Ico (0: ℕ) (2 ^ n), tiny_interval n i) := by
    unfold tiny_interval
    ext x
    constructor <;> intro H
    . simp at H ⊢
      obtain ⟨H, H0⟩ := H
      obtain H1 | H1 := Or.symm (LE.le.gt_or_eq H)
      . left
        exact H1
      . right
        use (Int.ceil (x * (2: ℝ) ^ n - 1)).natAbs

        have H2: 0 < (2: ℝ) ^ n := by
          norm_cast
          exact Nat.two_pow_pos n
        have H3: 0 < x * (2: ℝ) ^ n := mul_pos H1 H2

        have H7 (w: ℤ) (Hw: 0 ≤ w): (w: ℝ) = ↑(w.natAbs) := by
          rw [Int.cast_natAbs, abs_of_nonneg]
          exact Hw

        have H6: 0 ≤ Int.ceil (x * (2: ℝ) ^ n - 1) := by
          simp; exact H1

        have H4: (Int.ceil (x * (2: ℝ) ^ n - 1)).natAbs < x * (2: ℝ) ^ n := by
          have H5: Int.ceil (x * (2: ℝ) ^ n) - 1 < x * (2: ℝ) ^ n := by
            rw [<- Int.le_ceil_iff]
          rw [<- H7 _ (by linarith)]
          simp
          exact H5

        refine ⟨?_, ?_, ?_⟩
        . exact (div_lt_iff₀ H2).mpr H4
        . have H8: x * (2: ℝ) ^ n ≤ (2: ℝ) ^ n := by
            nlinarith
          rw [<- H7 _ (by simp; exact H1)] at H4
          have H9: (⌈x * 2 ^ n - 1⌉: ℝ) < (2: ℝ) ^ n := by
            exact gt_of_ge_of_gt H8 H4
          rw [H7 _ (by linarith)] at H9
          norm_cast at H9 ⊢
        . rw [<- H7 _ H6]
          simp
          rw [le_div_iff₀ H2]
          exact Int.le_ceil (x * 2 ^ n)

    . simp at H ⊢
      obtain H | H := H
      . subst x
        simp
      .
        obtain ⟨i, H0, H1, H2⟩ := H
        have H3: 0 < (2: ℝ) ^ n := by norm_cast; exact Nat.two_pow_pos n
        have H4: 0 ≤ (i: ℝ) / (2: ℝ) ^ n := by
          apply div_nonneg (Nat.cast_nonneg' i)
          linarith
        constructor
        . linarith
        . have H5: ((i: ℝ) + 1) / (2: ℝ) ^ n ≤ 1 := by
            have H6: (i: ℝ) + 1 ≤ (2: ℝ) ^ n := by
              norm_cast
            exact (div_le_one₀ H3).mpr H6
          apply le_trans H2 H5

  -- all these tiny intervals are disjoint.
  -- this fact is necessary for counting all the roots from all the intervals
  have roots_of_tiny_intervals_disjoint (n i j: ℕ) (Hne: i ≠ j):
      Disjoint {x | x ∈ tiny_interval n i ∧ f n x = x} {x | x ∈ tiny_interval n j ∧ f n x = x} := by
    unfold Disjoint
    simp
    intros s H1 H2
    ext x
    simp
    intros H3
    unfold tiny_interval at *
    have H1x := H1 H3
    have H2x := H2 H3
    simp at H1x H2x
    obtain ⟨⟨H4, H5⟩, H6⟩ := H1x
    obtain ⟨⟨H7, H8⟩, H9⟩ := H2x

    have Hn: 0 < (2: ℝ) ^ n := by
      norm_cast
      exact Nat.two_pow_pos n

    have H9: (i: ℝ) < x * (2: ℝ) ^ n := by
      have H9: (i: ℝ) / (2: ℝ) ^ n * (2: ℝ) ^ n < x * (2: ℝ) ^ n := by
        exact (mul_lt_mul_iff_of_pos_right Hn).mpr H4
      exact (mul_inv_lt_iff₀ Hn).mp H4

    have H10: x * (2: ℝ) ^ n ≤ (i: ℝ) + 1 := by
      exact (le_div_iff₀ Hn).mp H5

    have H11: (j: ℝ) < x * (2: ℝ) ^ n := by
      have H12: (j: ℝ) / (2: ℝ) ^ n * (2: ℝ) ^ n < x * (2: ℝ) ^ n := by
        exact (mul_lt_mul_iff_of_pos_right Hn).mpr H7
      exact (mul_inv_lt_iff₀ Hn).mp H7

    have H13: x * (2: ℝ) ^ n ≤ (j: ℝ) + 1 := by
      exact (le_div_iff₀ Hn).mp H8

    have Hlt: i < j ∨ j < i := by omega
    obtain Hlt | Hlt := Hlt
    . have H12: (i: ℝ) + 1 ≤ (j: ℝ) := by
        norm_cast
      linarith
    . have H12: (j: ℝ) + 1 ≤ (i: ℝ) := by
        norm_cast
      linarith


  -- the final part of the proof: we prove the fact about cardinality of set of roots
  -- for general `n`
  have general_goal (n: ℕ): {x | 0 ≤ x ∧ x ≤ 1 ∧ f n x = x}.ncard = 2 * 2 ^ n := by
    have aux (x: ℝ): 0 ≤ x ∧ x ≤ 1 ↔ x ∈ Icc 0 1 := by
      simp

    simp_rw [<- and_assoc, aux]
    rw [interval_zero_to_one_as_union n]

    have H: {x | x ∈ {0} ∪ ⋃ i ∈ Ico 0 (2 ^ n), tiny_interval n i ∧ f n x = x} =
            {x | x ∈ (⋃ i ∈ Ico (0: ℕ) (2 ^ n), tiny_interval n i) ∧ f n x = x} := by
      ext x
      simp
      intros H H0
      subst x
      rw [formula n 0 0] at H
      . norm_num at H
      . exact Nat.two_pow_pos n
      . simp

    rw [H]; clear H

    have H: {x | x ∈ (⋃ i ∈ Ico (0: ℕ) (2 ^ n), tiny_interval n i) ∧ f n x = x} =
            ⋃ i ∈ Ico (0: ℕ) (2 ^ n), { x ∈ tiny_interval n i | f n x = x} := by
      ext x
      simp
      tauto

    rw [H]; clear H

    rw [ncard_of_iUnion_of_disjoint_finite_sets_as_sum (2 ^ n)]
    . simp
      rw [Finset.sum_const_nat (m := 2)]
      . simp
        rw [mul_comm]
      . simp
        apply number_of_roots_in_each_interval
    . intros i j Hi Hj Hne
      exact roots_of_tiny_intervals_disjoint n i j Hne
    . intros i Hi
      apply Set.finite_of_ncard_pos
      rw [number_of_roots_in_each_interval n i Hi]
      norm_num

  -- rest is easy :)
  rw [general_goal]
  rfl