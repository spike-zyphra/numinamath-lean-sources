import Mathlib

open Finset Int Nat

/- Let $a_{1}, a_{2}, \ldots, a_{n}$ be distinct positive integers. Prove that


$$

\left(a_{1}^{7}+a_{2}^{7}+\cdots+a_{n}^{7}\right)+\left(a_{1}^{5}+a_{2}^{5}+\cdots+a_{n}^{5}\right) \geq 2\left(a_{1}^{3}+a_{2}^{3}+\cdots+a_{n}^{3}\right)^{2}

$$
 -/

theorem inequalities_222354 (n : ℕ) (hn : 0 < n) (a : ℕ → ℤ)
    (ha : ∀ i j, i < j → a i < a j) (ha' : ∀ i, 0 < a i) :
    (∑ i ∈ range n, a i ^ 7) + (∑ i ∈ range n, a i ^ 5) ≥
    2 * (∑ i ∈ range n, a i ^ 3) ^ 2 := by
  have : 1 ≤ n := by linarith
  -- Use induction on n
  induction n, this using le_induction with
  -- Base case
  | base =>
    simp
    rw [← pow_mul]
    norm_num
    -- Factor out (a 0)^5 and then factor a square
    suffices 0 ≤ (a 0)^5 * (a 0 - 1)^2 by
      rw [sub_sq] at this
      linarith
    -- We need to prove (a 0)^5 and (a 0 - 1)^2 are nonnegative
    apply mul_nonneg
    · exact pow_nonneg (show 0 ≤ a 0 by linarith [ha' 0]) 5
    -- Trivial inequality
    nlinarith
  -- Induction step
  | succ k hk ih' =>
    -- Make the induction hypothesis more usable
    have ih : _ := ih' (by linarith)
    clear ih'
    -- Convert to le instead of ge
    rw [ge_iff_le] at ih
    rw [ge_iff_le]
    -- Expand the square
    suffices 2 * (∑ i ∈ range k, a i ^ 3)^2 + 2 * (a k ^ 6 + 2 * ∑ i ∈ range k, a i ^ 3 * a k ^ 3) ≤ (∑ i ∈ range k, a i ^ 7) + (∑ i ∈ range k, a i ^ 5) + a k^5 + a k^7 by
      conv_rhs =>
        -- Split off last term
        repeat rw [sum_range_succ]
      conv_lhs =>
        -- Split off last term
        rw [sum_range_succ]
        -- Expand square
        rw [add_sq, add_assoc, mul_add, mul_assoc, sum_mul, ← pow_mul]
        norm_num
      -- Rearrange terms
      linarith
    rw [add_assoc]
    apply Int.add_le_add
    · -- Use the induction hypothesis
      exact ih
    -- Factor out a k ^ 3 from both sides
    rw [show a k ^ 6 = a k ^ 3 * a k ^ 3 by ring, ← sum_mul, mul_comm (∑ i ∈ range k, _) (a k ^ 3), ← mul_assoc, mul_comm 2 (a _ ^ 3), mul_assoc, ← mul_add, ← mul_assoc, mul_comm 2, mul_assoc]
    rw [show a k ^ 5 + a k ^ 7 = a k ^ 3 * (a k ^ 4 + (a k ^ 2)) by ring]
    -- Cancel out the a k ^ 3 and distribute factor of 2
    rw [mul_le_mul_left (pow_pos (ha' k) 3), mul_add, ← mul_assoc]
    norm_num
    -- Subtract
    suffices 4 * ∑ i ∈ range k, a i ^ 3 ≤ a k ^ 4 - 2 * a k ^ 3 + a k ^ 2 by
      linarith
    -- Factor as a square again
    rw [show a k ^ 4 - 2 * a k ^ 3 + a k ^ 2 = ((a k - 1) * a k) ^ 2 by ring]
    -- Variation on the classic 1 ^ 3 + ⋯ + n ^ 3 = (1 + ⋯ + n) ^ 2
    have sum_cubes (n : ℤ) : 0 < n → ((n - 1) * n) ^ 2 = 4 * ∑ i ∈ range (n.toNat), i ^ 3 := by
      intro hn
      -- Match statement is used to convert to Nat
      match n with
      | ofNat k =>
        simp at hn
        simp
        -- Use induction on k
        have : 1 ≤ k := by linarith
        induction k, this using le_induction with
        -- Base case is trivial
        | base => simp
        | succ m hm ih' =>
          simp
          norm_cast
          norm_cast at ih'
          -- Break off the last term
          rw [sum_range_succ, mul_add 4, ← ih' (show 0 < m by linarith)]
          zify
          simp [hm]
          -- Computation
          ring
    rw [sum_cubes _ (ha' _)]
    -- Divide by 4
    rw [_root_.mul_le_mul_left (by simp)]
    -- Use induction on k
    clear hn
    clear ih
    induction k, hk using le_induction with
    | base =>
      simp
      calc
        -- Compare a 0 ^ 3 to a sum over a range
        a 0 ^ 3 ≤ ∑ i ∈ range ((a 0).toNat + 1), i ^ 3 := by
          rw [sum_range_succ]
          simp
          rw [max_eq_left (by linarith [ha' 0])]
          -- The other terms are all fluff
          have : 0 ≤ ∑ i ∈ range (a 0).toNat, i ^ 3 := by
            apply sum_nonneg
            intro i hi
            positivity
          linarith
        _ ≤ ∑ i ∈ range (a 1).toNat, i ^ 3 := by
          simp
          -- Show sum is ≤ by showing it is a sum over a subset
          apply sum_le_sum_of_subset_of_nonneg
          · simp
            nth_rw 1 [show 1 = (1 : ℤ).toNat by simp, ← toNat_add]
            apply toNat_le_toNat
            · linarith [ha 0 1 (by linarith)]
            · linarith [ha' 0]
            simp
          intro i hi hi'
          positivity
      simp
    | succ m hm ih =>
      -- Break off a term
      rw [sum_range_succ]
      -- Use the induction hypothesis
      trans ∑ i ∈ range (a m).toNat, i ^ 3 + a m ^ 3
      · linarith
      -- Simplify the LHS
      simp
      rw [show a m ^ 3 = ((a m).toNat : ℤ) ^ 3 by simp; rw [max_eq_left]; linarith [ha' m], ← sum_range_succ]
      nth_rw 1 [show 1 = (1 : ℤ).toNat by simp, ← toNat_add (by linarith [ha' m]) (by simp)]
      -- Show that range (a m + 1).toNat ⊆ range (a (m + 1)).toNat
      apply sum_le_sum_of_subset_of_nonneg
      · simp
        left
        linarith [ha m (m + 1) (by linarith)]
      intro i hi hi'
      positivity