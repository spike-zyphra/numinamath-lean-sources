import Mathlib

-- Lemma stating that 2 divides the product of n and (n+1) for any natural number n.
-- This is because either n is even or n+1 is even.
@[simp] lemma lemma1 ( n : ℕ ) : 2 ∣ n * (n + 1) := by 
  -- Case analysis on whether 2 divides n.
  by_cases hn : 2 ∣ n
  -- If 2 divides n, then 2 divides n * (n+1) because n is a factor.
  exact Dvd.dvd.mul_right hn (n + 1)
  -- If 2 does not divide n, then n is odd.
  -- Rewrite '¬ (2 ∣ n)' to 'n is not even' using the equivalence between divisibility by 2 and evenness.
  rw [← @even_iff_two_dvd] at hn
  -- Rewrite 'n is not even' to 'n is odd'.
  rw [@Nat.not_even_iff_odd] at hn
  -- Rewrite 'n is odd' to 'there exists n' such that n = 2*n' + 1' (using bit1 representation).
  rw [@odd_iff_exists_bit1] at hn
  -- Obtain n' and the evidence hn' that n = 2*n' + 1.
  obtain ⟨n', hn'⟩ := hn
  -- Substitute n with 2*n' + 1 in the goal expression.
  subst hn'
  -- The goal becomes 2 ∣ (2*n' + 1) * (2*n' + 1 + 1).
  -- This simplifies to 2 ∣ (2*n' + 1) * (2*n' + 2).
  -- We need to provide a k such that (2*n' + 1) * (2*n' + 2) = 2 * k.
  -- Let k = (2*n' + 1) * (n' + 1), since (2*n' + 2) = 2 * (n' + 1).
  use (2 * n' + 1) * (n' + 1)
  -- Prove that (2*n' + 1) * (2*n' + 1 + 1) = 2 * ((2 * n' + 1) * (n' + 1)) by ring normalization.
  ring


-- Lemma stating that n choose 1 is n, for n ≥ 1.
@[simp] lemma lemma2 ( n : ℕ ) ( hn : 1 ≤ n ) : n.choose 1 = n := by
  -- Induction on n, using Nat.le_induction.
  -- This form of induction allows assuming the property for all m < n that satisfy the condition.
  -- `n` is the number we are proving for, `hn` is the condition `1 ≤ n`.
  induction n, hn using Nat.le_induction with
  -- Base case of the induction:
  -- This case is triggered for the smallest n satisfying `1 ≤ n`, which is n=1.
  -- Goal: 1.choose 1 = 1. This is true by definition of `choose`.
  | base => rfl
  -- Inductive step:
  -- `n` here is the current number (greater than the base case).
  -- `hn` is the hypothesis `1 ≤ n`.
  -- `ih` is the induction hypothesis: `∀ m < n, (1 ≤ m → m.choose 1 = m)`.
  | succ n hn ih =>
    -- Unfold the definition of Nat.choose for n.choose 1.
    -- For n > 0, n.choose 1 expands using Pascal's recurrence:
    -- n.choose 1 = (n-1).choose 0 + (n-1).choose 1.
    -- This relies on `Nat.choose_succ_succ` or similar definition: `choose (m+1) (k+1) = choose m k + choose m (k+1)`.
    -- So, `n.choose 1 = (n-1).choose (0) + (n-1).choose 1`.
    unfold Nat.choose
    -- Simplify the expression using known lemmas:
    -- `Nat.choose_zero_right`: (n-1).choose 0 = 1 (if n-1 is a natural number, i.e. n ≥ 1).
    -- `ih`: applies to (n-1).choose 1.
    --   If 1 ≤ n-1 (i.e. n ≥ 2), then `ih (n-1) (Nat.lt_of_succ_le hn) (H_1_le_n_minus_1)` yields `(n-1).choose 1 = n-1`.
    --   If n=1, then n-1=0. `0.choose 1 = 0`. The `ih` is not used in this way for `m=0`.
    --   `simp` handles these cases. `(n-1).choose 1` becomes `n-1` (if `n-1 ≥ 1`) or `0` (if `n-1=0`).
    -- So, if n ≥ 2: `1 + (n-1)`.
    -- If n = 1: `1 + 0.choose 1 = 1 + 0 = 1`. (Matches `n=1`).
    -- `zero_add` is likely used if some term becomes `0 + X`.
    simp only [Nat.choose_zero_right, zero_add, ih]
    -- The expression simplifies to `1 + (n-1)` (or `n` if `n-1` was handled by `ih` already).
    -- `ring` proves `1 + (n-1) = n`.
    ring

-- Lemma stating that n choose 2 is n * (n - 1) / 2, for n ≥ 2.
@[simp] lemma lemma3 ( n : ℕ ) ( hn : 2 ≤ n ) : n.choose 2 = n * (n - 1) / 2 := by
  -- Induction on n, using Nat.le_induction.
  -- `n` is the number we are proving for, `hn` is the condition `2 ≤ n`.
  induction n, hn using Nat.le_induction with
  -- Base case: Smallest n satisfying `2 ≤ n`, which is n=2.
  -- Goal: 2.choose 2 = 2 * (2-1) / 2.
  -- 2.choose 2 = 1. RHS: 2 * 1 / 2 = 1. True by definition.
  | base => rfl
  -- Inductive step:
  -- `n` is the current number (n > 2 or n=2 handled by base if not strictly >).
  -- `hn` is `2 ≤ n`.
  -- `ih` is `∀ m < n, (2 ≤ m → m.choose 2 = m * (m-1)/2)`.
  | succ n hn ih =>
    -- Unfold n.choose 2 using Pascal's recurrence:
    -- n.choose 2 = (n-1).choose 1 + (n-1).choose 2. (Requires n ≥ 1, k=1 here for choose k)
    unfold Nat.choose
    -- Simplify the expression:
    -- `Nat.choose_one_right`: (n-1).choose 1 = n-1 (requires 1 ≤ n-1, true if n ≥ 2 from `hn`).
    -- `ih`: (n-1).choose 2 = (n-1)*(n-2)/2 (requires 2 ≤ n-1, i.e. n ≥ 3).
    --   If n=2, (n-1).choose 2 = 1.choose 2 = 0. Formula (1)*(1-2)/2 is problematic in Nat.
    --   The `ih` applies to `m=n-1` if `n-1 ≥ 2`. `simp` handles the case n=2 where (n-1)=1, so `1.choose 2 = 0`.
    -- `Nat.reduceAdd` performs simplifications on additions.
    -- `add_tsub_cancel_right` might simplify e.g. `(n-1)+1`.
    simp only [Nat.choose_one_right, Nat.reduceAdd, ih, add_tsub_cancel_right]
    -- After simp, goal is: (n-1) + (n-1)*(n-2)/2 = n*(n-1)/2. (Assuming n ≥ 3 for (n-2) or handled by simp if n=2).
    clear ih -- The hypothesis `ih` is no longer needed.
    -- To eliminate denominators, multiply both sides of the equality by 2.
    -- `mul_right_cancel₀ h_c_ne_zero : (a*c = b*c ↔ a=b)`. We want to prove `LHS = RHS`.
    -- This is equivalent to proving `LHS * 2 = RHS * 2`, given `2 ≠ 0`.
    apply mul_right_cancel₀ (show 2 ≠ 0 by decide)
    -- Goal: 2 * ((n-1) + (n-1)*(n-2)/2) = 2 * (n*(n-1)/2).
    -- Apply distributivity and cancel divisions. The `rw` combines multiple steps:
    -- 1. `add_mul`: `2 * (A + B)` becomes `2*A + 2*B`.
    --    LHS: `2*(n-1) + 2*((n-1)*(n-2)/2)`.
    -- 2. First `Nat.div_mul_cancel`: `2*((n-1)*(n-2)/2)` becomes `(n-1)*(n-2)`.
    --    This requires `2 ∣ (n-1)*(n-2)`, proved by the `match n with ...` block.
    --    LHS is now `2*(n-1) + (n-1)*(n-2)`.
    -- 3. Second `Nat.div_mul_cancel`: `2 * (n*(n-1)/2)` (on RHS) becomes `n*(n-1)`.
    --    This requires `2 ∣ n*(n-1)`, proved by `rw [mul_comm]; exact lemma1 (n-1)`.
    --    RHS is now `n*(n-1)`.
    -- Current goal: `2*(n-1) + (n-1)*(n-2) = n*(n-1)`.
    -- 4. `mul_comm` (implicitly, on `2*(n-1)` to `(n-1)*2`) then `← mul_add` (factor out `(n-1)`):
    --    `(n-1)*2 + (n-1)*(n-2)` becomes `(n-1) * (2 + (n-2))`.
    --    LHS: `(n-1) * (2 + (n-2))`.
    -- 5. `add_comm 2 _`: `2 + (n-2)` becomes `(n-2) + 2`. (No, this swaps operands of `+` if needed by `Nat.sub_add_cancel`).
    --    LHS: `(n-1) * ((n-2) + 2)`.
    -- 6. `mul_comm` on RHS: `n*(n-1)` becomes `(n-1)*n`.
    -- Current goal: `(n-1) * ((n-2) + 2) = (n-1)*n`.
    rw [add_mul, Nat.div_mul_cancel, Nat.div_mul_cancel, ← mul_add, add_comm 2, mul_comm]
    -- `congr 1` reduces the goal from `(n-1)*X = (n-1)*Y` to `X = Y`, assuming `n-1` is not a special value like zero.
    -- (More accurately, `f x = f y` to `x = y` if `f` is injective, or `A*X = A*Y` to `X=Y` if `A` is cancellative).
    -- Here, it means we need to prove `(n-2)+2 = n`.
    -- The `rw [show n - 1 + 2 = ...]` seems to be a leftover or a slight misdirection in my trace; the goal is simpler.
    -- It should be `(n-2)+2 = n`.
    congr 1; rw [show n - 1 + 2 = n - 1 + 1 + 1 by rfl]; simp only [add_left_inj]
    -- Goal is `(n-2)+2 = n`.
    -- `Nat.sub_add_cancel` states `(a-b)+b = a` if `b ≤ a`. Here `a=n, b=2`.
    -- This requires `2 ≤ n`, which is given by `hn`. `linarith` proves this condition.
    refine Nat.sub_add_cancel ?_; linarith
    -- Proof for the first `Nat.div_mul_cancel` (LHS): `2 ∣ (n-1)*(n-2)`.
    -- This is equivalent to `2 ∣ m*(m+1)` where `m = n-2`. This is true by `lemma1 (n-2)`.
    rw [mul_comm]; exact lemma1 n
    match n with
    | 0 => contradiction -- Ruled out by hn: 2 ≤ n.
    -- Case `n` is `k+1`. So `n-1` is `k`, `n-2` is `k-1`. We need `2 ∣ k*(k-1)`.
    -- `add_tsub_cancel_right` simplifies `(k+1)-1` to `k`.
    -- `mul_comm _ k`: `k*(k-1)` or `(k-1)*k`.
    -- `lemma1 (k-1)` proves `2 ∣ (k-1)*k`.
    | n + 1 => simp only [add_tsub_cancel_right, mul_comm _ n, lemma1] -- `n` here is the `k` in my comment.
    -- Proof for the second `Nat.div_mul_cancel` (RHS): `2 ∣ n*(n-1)`.
    -- `mul_comm` makes it `(n-1)*n`. `lemma1 (n-1)` proves `2 ∣ (n-1)*n`.

-- The following theorem proves an algebraic equivalence.
-- It states that the equation (n choose 2) - (n choose 1) + 1 = 15
-- holds if and only if n is equal to 7, for natural numbers n ≥ 2.
-- Note: The "human_proof" provided in the prompt refers to a different problem
-- ($C(n, n/3) = 15 \implies n=6$), so its specific steps are not directly applicable here.
-- However, this theorem is similar in that it solves an equation involving binomial coefficients.
theorem algebra_229393 {n : ℕ} (hn : n ≥ 2) :
  (n.choose 2) - (n.choose 1) + 1 = 15 ↔ n = 7 := by
  -- Rewrite (n.choose 2) and (n.choose 1) using the lemmas proved above.
  -- (n.choose 2) becomes n*(n-1)/2. (Requires 2 ≤ n, given by hn).
  -- (n.choose 1) becomes n. (Requires 1 ≤ n, implied by hn: 2 ≤ n).
  rw [lemma3, lemma2]
  -- The rewrites generate side goals for their conditions (e.g., `2 ≤ n` for `lemma3`).
  -- `linarith` solves these using the hypothesis `hn : n ≥ 2`.
  -- `repeat on_goal 2 => linarith` applies `linarith` to the 2nd and subsequent generated goals.
  repeat on_goal 2 => linarith
  -- The equation is now: `n*(n-1)/2 - n + 1 = 15 ↔ n = 7`.
  -- This can be rewritten by noting `-n+1 = -(n-1)`. So: `n*(n-1)/2 - (n-1) = 15-1 = 14`.
  -- No, it's `n*(n-1)/2 - (n-1) = 15` if we don't subtract 1 from both sides.
  -- The equation `n*(n-1)/2 - n + 1 = 15` is `(n*(n-1)/2 - n) + 1 = 15` (since `n ≤ n*(n-1)/2` for `n≥2` except n=2 `1-2` is 0).
  -- For n=2: `1-2+1 = 0+1 = 1`. For n=3: `3-3+1 = 0+1 = 1`. For n=4: `6-4+1 = 2+1 = 3`.
  -- So, the equation `LHS = 15` is what `mul_left_inj'` is applied to.
  -- To eliminate the division by 2, multiply the equality `n*(n-1)/2 - n + 1 = 15` by 2.
  -- `mul_left_inj' c_ne_zero` rewrites `A = B` to `c*A = c*B`.
  rw [← mul_left_inj' (show 2 ≠ 0 by decide)]
  -- The equation becomes: `2 * (n*(n-1)/2 - n + 1) = 2 * 15 ↔ n = 7`.
  -- This simplifies (distributing 2 and cancelling): `n*(n-1) - 2*n + 2 = 30 ↔ n = 7`.
  -- This step requires properties like `2 ∣ n*(n-1)` and rules for distributing multiplication over Nat subtraction.
  -- These side goals are handled implicitly or by later `on_goal` tactics.
  -- The expression `n*(n-1) - 2*n + 2` is `n*n - n - 2*n + 2 = n*n - 3*n + 2`.
  -- `ring_nf` normalizes this polynomial expression.
  -- `Nat.sub_mul` is `(a-b)*c = ac-bc`. Its specific use here might be for internal simplification steps
  -- done by `ring_nf` or to handle specific Nat subtraction properties.
  ring_nf; rw [Nat.sub_mul]
  -- Current state: `n*n - 3*n + 2 = 30 ↔ n = 7`.
  -- Proceed by cases on n.
  match n with
  -- Case n = 0: Contradicts `hn : n ≥ 2`.
  | 0 => contradiction
  -- Case n = 1: Contradicts `hn : n ≥ 2`.
  | 1 => contradiction
  -- Case n = 2: Goal is `2*2 - 3*2 + 2 = 30 ↔ 2 = 7`.
  -- LHS: `4 - 6 + 2 = 0 + 2 = 2` (in Nat arithmetic, `4-6=0`).
  -- So `2 = 30 ↔ 2 = 7`. This is `False ↔ False`, which is True. `simp` proves this.
  | 2 => simp only [Nat.add_one_sub_one, mul_one, Nat.ofNat_pos, Nat.div_self, one_mul, Nat.reduceMul,
    Nat.reduceLeDiff, Nat.sub_eq_zero_of_le, add_zero, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff]
  -- Case n = 3: Goal is `3*3 - 3*3 + 2 = 30 ↔ 3 = 7`. LHS: `9 - 9 + 2 = 2`. `2 = 30 ↔ 3 = 7` (F ↔ F, True).
  | 3 => simp only [Nat.add_one_sub_one, Nat.reduceMul, Nat.reduceDiv, tsub_self, add_zero,
    OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff]
  -- Case n = 4: Goal is `4*4 - 3*4 + 2 = 30 ↔ 4 = 7`. LHS: `16 - 12 + 2 = 6`. `6 = 30 ↔ 4 = 7` (F ↔ F, True).
  | 4 => simp only [Nat.add_one_sub_one, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd,
    OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff]
  -- Case n = 5: Goal is `5*5 - 3*5 + 2 = 30 ↔ 5 = 7`. LHS: `25 - 15 + 2 = 12`. `12 = 30 ↔ 5 = 7` (F ↔ F, True).
  | 5 => simp only [Nat.add_one_sub_one, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd,
    OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff]
  -- Case n = 6: Goal is `6*6 - 3*6 + 2 = 30 ↔ 6 = 7`. LHS: `36 - 18 + 2 = 20`. `20 = 30 ↔ 6 = 7` (F ↔ F, True).
  | 6 => simp only [Nat.add_one_sub_one, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd,
    OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff]
  -- Case n = 7: Goal is `7*7 - 3*7 + 2 = 30 ↔ 7 = 7`. LHS: `49 - 21 + 2 = 30`. `30 = 30 ↔ 7 = 7` (T ↔ T, True).
  | 7 => simp only [Nat.add_one_sub_one, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd,
    OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff]
  -- Case `original_n = m + 8` (where `m` is the `n` in this `match` arm, so `original_n ≥ 8`).
  | n + 8 => -- `n` here is `m` from my comment. `original_n = m+8`.
    -- Goal: `(m+8)*(m+8) - 3*(m+8) + 2 = 30 ↔ m+8 = 7`.
    -- `Nat.reduceEqDiff` simplifies `m+8 = 7` to `False` (since `m+8 ≥ 8`).
    -- `iff_false` rewrites `(P ↔ False)` to `¬P`.
    -- `ne_eq` rewrites `¬(A=B)` to `A ≠ B`.
    -- `clear hn` as `m+8 ≥ 2` is now evident.
    simp only [Nat.add_one_sub_one, Nat.reduceEqDiff, iff_false, ne_eq]; clear hn
    -- Goal is now: `(m+8)*(m+8) - 3*(m+8) + 2 ≠ 30`.
    -- The `on_goal 2 => ...` handles a side goal, likely from `rw [← mul_left_inj' ...]`.
    -- This side goal is likely proving `2 ∣ X*Y` for some X,Y.
    rw [Nat.div_mul_cancel]
    on_goal 2 => rw [mul_comm]; simp only [Nat.add_one_sub_one, lemma1]
    -- For the main goal `(m+8)*(m+8) - 3*(m+8) + 2 ≠ 30`:
    -- `rw [← Nat.mul_sub]` (i.e. `A*C - B*C = (A-B)*C`) is used to factor the expression.
    -- `(m+8)*(m+8) - 3*(m+8)` becomes `((m+8)-3)*(m+8)`.
    -- So LHS becomes `((m+8)-3)*(m+8) + 2`.
    rw [← Nat.mul_sub]
    -- `simp only [Nat.reduceSubDiff]` simplifies `(m+8)-3` to `m+5`.
    -- LHS is now `(m+5)*(m+8) + 2`.
    simp only [Nat.reduceSubDiff]
    -- `ring_nf` expands `(m+5)*(m+8) + 2`:
    -- `(m*m + 8*m + 5*m + 40) + 2 = m*m + 13*m + 40 + 2 = m*m + 13*m + 42`.
    ring_nf
    -- Goal is now: `m*m + 13*m + 42 ≠ 30`.
    -- To show this, observe that `m*m + 13*m ≥ 0` for `m : ℕ`.
    -- Thus, `m*m + 13*m + 42 ≥ 42`.
    -- Since `42 > 30`, `m*m + 13*m + 42` can never be equal to `30`.
    -- `rw [add_comm 42, add_right_comm]` reorders terms to make this obvious for `simp`.
    -- e.g., `X + 42 = 30` implies `X + 12 + 30 = 30` implies `X+12=0`, impossible for Nat X unless X=0 and 12=0.
    -- `Nat.reduceEqDiff` simplifies `(some_val_ge_42) = 30` to `False`.
    -- `not_false_eq_true` changes `¬False` to `True`.
    rw [add_comm 42, add_right_comm]; simp only [Nat.reduceEqDiff, not_false_eq_true]
