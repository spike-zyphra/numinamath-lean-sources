import Mathlib

/-Consider $0<\lambda<1$, and let $A$ be a multiset of positive integers. Let $A_{n}=\{a \in$ $A: a \leq n\}$. Assume that for every $n \in \mathbb{N}$, the multiset $A_{n}$ contains at most $n \lambda$ numbers. Show that there are infinitely many $n \in \mathbb{N}$ for which the sum of the elements in $A_{n}$ is at most $\frac{n(n+1)}{2} \lambda$.
-/
theorem number_theory_605284 (lambda : ℝ) (hl : 0 < lambda ∧ lambda < 1)
  (A : Finset ℕ) (hA : ∀ n ∈ A, 0 < n)
  (_hA' : ∀ n, A.filter (fun x => x ≤ n) ⊆ Finset.Icc 1 n)
  (_hA'' : ∀ n, (A.filter (fun x => x ≤ n)).card ≤ n * lambda) :
  ∀ N, ∃ n, n > N ∧ ∑ i ∈ A.filter (fun x => x ≤ n), i ≤ (n * (n + 1)) / 2 * lambda := by
  -- We need to show this for any N.
  intro N; clear _hA' _hA''
  -- The set A is either empty or non-empty.
  have hA_empty_or_nonempty : A = ∅ ∨ ∃ a, a ∈ A := Finset.eq_empty_or_nonempty A
  -- We proceed by cases on whether A is empty or non-empty.
  cases hA_empty_or_nonempty with
  -- Case 1: A is empty.
  | inl hA_empty =>
    -- If A is empty, we can choose n = N + 1.
    use N + 1
    -- We need to prove two things: n > N and the sum condition.
    constructor
    -- First goal: N + 1 > N.
    · simp only [gt_iff_lt, lt_add_iff_pos_right, zero_lt_one] -- This simplifies to 0 < 1, which is true.
    -- Second goal: sum over (empty set) ≤ ((N + 1) * (N + 2) / 2) * lambda.
    · simp only [hA_empty, Finset.filter_empty, Finset.sum_empty, CharP.cast_eq_zero, Nat.cast_add,
      Nat.cast_one] -- The sum over an empty set is 0.
      -- We need to show 0 ≤ ((N + 1) * (N + 2) / 2) * lambda.
      have hlp := hl.1 -- lambda > 0.
      positivity -- Since N ≥ 0, (N+1)*(N+2)/2 is non-negative. Lambda is positive. So the product is non-negative.
  -- Case 2: A is non-empty.
  | inr ha =>
    -- Since A is non-empty, it contains some element 'a'.
    obtain ⟨a, ha⟩ := ha
    -- Let M be the maximum element in the non-empty set A.
    -- The existence of 'a' in A (from 'ha') ensures A is non-empty,
    -- so A.max' is well-defined.
    let M := A.max' ⟨a, ha⟩
    -- The maximum element M is a member of A.
    have hM_mem : M ∈ A := A.max'_mem ⟨a, ha⟩
    -- This local lemma states that for any n ≥ M (the maximum element of A),
    -- filtering A for elements ≤ n results in the entire set A.
    have h_le_max : ∀ n, n ≥ M → A.filter (fun x => x ≤ n) = A := by
      -- Introduce n and the hypothesis hn : n ≥ M.
      intro n hn
      -- To prove set equality, we show subset inclusion in both directions.
      refine Finset.Subset.antisymm_iff.mpr ?_; constructor
      -- First direction: A.filter (fun x => x ≤ n) ⊆ A. This is true by definition of filter.
      · exact Finset.filter_subset _ _
      -- Second direction: A ⊆ A.filter (fun x => x ≤ n).
      -- Take an arbitrary element x from A.
      · intro x hx_mem_A
        -- To show x ∈ A.filter (fun x => x ≤ n), we need to show x ∈ A and x ≤ n.
        simp only [Finset.mem_filter]
        constructor;
        -- The first part, x ∈ A, is true by assumption hx_mem_A.
        · exact hx_mem_A
        -- For the second part, x ≤ n:
        -- We know x ≤ M because M is the maximum element of A (A.max'_le_iff).
        -- We also have M ≤ n (from hn).
        -- By transitivity of ≤, x ≤ n.
        apply le_trans ((A.max'_le_iff ⟨a, ha⟩).1 (le_refl M) x hx_mem_A) hn
    -- Let S be the sum of all elements in the set A.
    -- Since A is a Finset ℕ, S is a natural number.
    let S := ∑ i ∈ A, i
    -- (2 : ℝ) is positive.
    have two_pos : (2 : ℝ) > 0 := by norm_num
    -- This local lemma proves that 2 * S / lambda is positive.
    have h_pos_div : 0 < 2 * S / lambda := by
      -- A division a/b is positive if a and b have the same sign. Here, both are positive.
      apply div_pos
      -- Numerator 2 * S is positive.
      apply mul_pos
      -- 2 is positive.
      · linarith [two_pos]
      -- S (cast to real) is positive.
      · simp only [Nat.cast_pos] -- This requires S > 0 as a natural number.
        -- The sum of elements in a Finset is positive if all elements are positive and the set is non-empty.
        apply Finset.sum_pos
        -- hA ensures all elements in A are positive.
        exact hA
        -- ⟨a, ha⟩ ensures A is non-empty.
        exact ⟨a, ha⟩
      -- Denominator lambda is positive (from hl.1).
      · exact hl.1

    -- By the Archimedean property, there exists a natural number N'
    -- such that N' > sqrt(2 * S / lambda).
    obtain ⟨N', hN'⟩ := exists_nat_gt (Real.sqrt (2 * S / lambda))

    -- If (N' : ℝ) > sqrt(2 * S / lambda), then (N' : ℝ)^2 > 2 * S / lambda.
    -- This holds because N' is positive and 2 * S / lambda is positive.
    have h_sq : (N' : ℝ) ^ 2 > 2 * S / lambda := Real.lt_sq_of_sqrt_lt hN'

    -- This local lemma shows that for any n (implicitly n ≥ 0, as it's Nat cast to Real),
    -- (n * (n + 1) / 2) * lambda ≥ (n^2 / 2) * lambda.
    have h_quad_le : ∀ n, n ≥ N' → (n * (n + 1) / 2) * lambda ≥ (n ^ 2 / 2) * lambda := by
      intro n hn -- hn (n ≥ N') is not used in this specific proof but good for context.
      -- Rewrite n * (n + 1) as n^2 + n.
      calc (n * (n + 1) / 2) * lambda = ((n ^ 2 + n) / 2) * lambda := by ring
      -- To show ((n^2 + n)/2)*lambda ≥ (n^2/2)*lambda:
      _ ≥ (n ^ 2 / 2) * lambda := by
        -- Since lambda > 0 (hl.left), we can multiply/divide by lambda without changing inequality direction.
        -- So we need to show (n^2 + n)/2 ≥ n^2/2.
        simp only [ge_iff_le, hl.left, mul_le_mul_right]
        -- Since 2 > 0 (two_pos), (A/2) ≥ (B/2) iff A ≥ B.
        -- So we need to show n^2 + n ≥ n^2.
        refine (div_le_div_iff_of_pos_right two_pos).mpr ?_
        -- This simplifies to n ≥ 0, which is true for (n : ℕ).
        simp only [le_add_iff_nonneg_right, Nat.cast_nonneg]
    -- The specific inequality hN' (N' > sqrt(...)) is no longer needed directly, as h_sq captures its consequence.
    clear hN'

    -- This local lemma establishes a key inequality: (N' * (N' + 1) / 2) * lambda ≥ S.
    have hN'_final : (N' * (N' + 1) / 2) * lambda ≥ S := by
      -- We use transitivity of ≥.
      apply ge_trans
      -- First part: (N' * (N' + 1) / 2) * lambda ≥ (N'^2 / 2) * lambda.
      -- This follows from h_quad_le applied with n = N'.
      · apply h_quad_le _ (le_refl N')
      -- Second part (goal): (N'^2 / 2) * lambda ≥ S.
      -- We only need h_sq ( (N':ℝ)^2 > 2*S/lambda ) and hl (properties of lambda).
      · clear * - h_sq hl
        -- Rewrite h_sq from > to < for easier manipulation.
        simp only [gt_iff_lt] at h_sq -- h_sq is now 2 * S / lambda < (N' : ℝ)^2
        -- Rewrite /lambda as * lambda⁻¹.
        replace h_sq : 2 * ↑S * lambda⁻¹ < ↑N' ^ 2 := h_sq
        -- Using (X * Y⁻¹ < Z and Y > 0) ↔ (X < Z * Y).
        -- Here X = 2*S, Y = lambda, Z = (N')^2. lambda > 0 is from hl.1.
        -- So h_sq becomes 2 * S < (N')^2 * lambda.
        rw [@mul_inv_lt_iff₀ _ _ _ _ _ (↑N' ^ 2 : ℝ) (2 * ↑S : ℝ) lambda _ hl.1] at h_sq
        -- The goal is (N'^2 / 2) * lambda ≥ S, which is (N'^2 * lambda / 2) ≥ S.
        rw [@div_mul_eq_mul_div₀] -- Rearranges (N'^2 / 2) * lambda to N'^2 * lambda / 2.
        -- State the goal in a slightly different form.
        refine (?_ : ↑N' ^ 2 * lambda * 2⁻¹ ≥ ↑S)
        -- Rewrite ≥ as ≤ for the next step. Goal: S ≤ N'^2 * lambda * 2⁻¹.
        simp only [ge_iff_le]
        -- Using (A ≤ B * C⁻¹ and C > 0) ↔ (A * C ≤ B).
        -- Here A = S, B = N'^2 * lambda, C = 2. two_pos gives 2 > 0.
        -- Goal becomes S * 2 ≤ N'^2 * lambda.
        rw [propext (le_mul_inv_iff₀' two_pos)]
        -- This is 2 * S ≤ N'^2 * lambda, which follows from h_sq (2 * S < N'^2 * lambda).
        exact le_of_lt h_sq

    -- Define n as the maximum of (N + 1), M, and N'.
    -- This choice ensures:
    -- 1. n > N (because n ≥ N + 1).
    -- 2. n ≥ M (so that ∑_{i∈A, i≤n} i = S).
    -- 3. n ≥ N' (so that (n(n+1)/2)λ ≥ (N'(N'+1)/2)λ ≥ S).
    let n := (N + 1) ⊔ M ⊔ N'
    -- This n is our candidate.
    use n
    -- We need to prove n > N and the sum condition.
    constructor
    -- First goal: n > N.
    · simp only [gt_iff_lt, lt_sup_iff, left_lt_sup, not_le, n] -- n is ((N+1)⊔M)⊔N'. We need to show N < n.
      -- This simplifies to N < N+1 ∨ N < M ∨ N < N'.
      -- Since N < N+1 is true (0 < 1), the disjunction is true.
      simp only [lt_add_iff_pos_right, zero_lt_one, true_or]
    -- Second goal: ∑ i ∈ A.filter (fun x => x ≤ n), i ≤ (n * (n + 1)) / 2 * lambda.
    · exact calc
      -- Step 1: Show that the sum is equal to S.
      (↑(∑ i ∈ A.filter (fun x => x ≤ n), i):ℝ) = ↑S := by
        -- Substitute the definition of S.
        simp only [S]; push_cast
        -- We need to show equality of the sums, which means equality of the sets being summed over.
        congr
        -- Apply the lemma h_le_max, which states that if n ≥ M, then A.filter (fun x => x ≤ n) = A.
        apply h_le_max
        -- We need to show n ≥ M.
        -- n is (N+1) ⊔ M ⊔ N'. By definition of sup, n ≥ M.
        simp only [ge_iff_le, le_sup_iff, le_sup_right, true_or, n]
        simp only [le_refl, or_true, true_or]
      -- Step 2: Show S ≤ (n * (n + 1) / 2) * lambda.
      _ ≤ (n * (n + 1) / 2) * lambda := by
        -- We know from hN'_final that S ≤ (N' * (N' + 1) / 2) * lambda.
        -- By transitivity, if we show (N' * (N' + 1) / 2) * lambda ≤ (n * (n + 1) / 2) * lambda, we are done.
        apply le_trans hN'_final
        -- Goal is now: (N' * (N' + 1) / 2) * lambda ≤ (n * (n + 1) / 2) * lambda.
        -- Since lambda > 0 (hl.1), we can cancel lambda from both sides.
        · simp only [hl.1, mul_le_mul_right]
          -- Goal: (N' * (N' + 1) / 2) ≤ (n * (n + 1) / 2).
          -- Clear all hypotheses not relevant to N', n and basic arithmetic.
          clear * - -- The proof from here only depends on N', n and their properties.
          -- Since 2 > 0, we can multiply by 2 on both sides.
          refine (div_le_div_iff_of_pos_right ?_).mpr ?_
          · norm_num -- Proves (2:ℝ) > 0.
          -- Goal: N' * (N' + 1) ≤ n * (n + 1).
          -- This holds because N' ≤ n (since n = _ ⊔ N' ⊔ _) and k*(k+1) is an increasing function for k ≥ 0.
          -- Proof by steps: N'*(N'+1) ≤ n*(N'+1) ≤ n*(n+1).
          -- First, N' * (N' + 1) ≤ n * (N' + 1).
          haveI : (↑N' * (↑N' + 1):ℝ) ≤ n * (↑N' + 1) := by
            -- This uses a ≤ c implies a*b ≤ c*b if b ≥ 0. Here a=N', c=n, b=N'+1.
            refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
            -- Need to show N' ≤ n. True because n = _ ⊔ N' ⊔ _.
            simp only [Nat.cast_max, Nat.cast_add, Nat.cast_one, le_sup_right, n]
            -- This tactic handles the subgoal for N' ≤ n.
            on_goal 3 => positivity -- Need to show N'+1 ≥ 0. True since N' : ℕ.
            -- aesop solves remaining goals (e.g. reflexivity or simple type properties).
            all_goals aesop
          -- Apply transitivity using the above.
          apply this.trans
          -- Goal: n * (N' + 1) ≤ n * (n + 1).
          -- This uses b ≤ c implies a*b ≤ a*c if a ≥ 0. Here a=n, b=N'+1, c=n+1.
          refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
          -- This tactic handles the subgoal for n (non-negativity).
          on_goal 2 =>
            -- Need to show N'+1 ≤ n+1, which simplifies to N' ≤ n.
            simp only [Nat.cast_max, Nat.cast_add, Nat.cast_one, add_le_add_iff_right, le_sup_right, n]
          -- This tactic handles the subgoal for n ≥ 0. True since n : ℕ.
          on_goal 3 => positivity
          -- aesop solves remaining goals.
          all_goals aesop
