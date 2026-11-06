import Mathlib


/-
For any natural number  $n$ , consider a  $1\times n$  rectangular board made up of  $n$  unit squares. This is covered by  $3$  types of tiles :  $1\times 1$  red tile,  $1\times 1$  green tile and  $1\times 2$  domino. (For example, we can have  $5$  types of tiling when  $n=2$  : red-red ; red-green ; green-red ; green-green ; and blue.) Let  $t_n$  denote the number of ways of covering  $1\times n$  rectangular board by these  $3$  types of tiles. Prove that,  $t_n$  divides  $t_{2n+1}$ .
-/
theorem number_theory_8808
    (f : ℕ → ℕ)
    (h_f0 : f 0 = 1)
    (h_f1 : f 1 = 2)
    (h_fother : ∀ n, f (n + 2) = 2 * f (n + 1) + f n) :
    ∀ n, f n ∣ f (2 * n + 1) := by

  intro n

  -- Step 1: Understanding the Recurrence Relation
  
  -- The number of ways to tile a $1 \times n$ board, denoted by $ t_n $, satisfies the recurrence:
  -- $$
  -- t_n = 2t_{n-1} + t_{n-2}
  -- $$
  -- with initial conditions:
  -- $$
  -- t_0 = 1, \quad t_1 = 2
  -- $$
  

  -- Step 2: Solving the Recurrence Relation

  -- aux lemma, showing that `(1 - √ 2) ^ (n + 1) + (1 + √ 2) ^ (n + 1)` is a natural number
  have r1 : ∃ t : ℕ, t = (1 - √ 2) ^ (n + 1) + (1 + √ 2) ^ (n + 1) := by

    have r31 : ∀ k : ℕ,
        (∃ t : ℕ, (1 - √ 2) ^ k + (1 + √ 2) ^ k = t) ∧
        (∃ t : ℕ, ((1 + √ 2) ^ k - (1 - √ 2) ^ k) * √ 2 = t) := by
      intro k
      induction k with
      | zero =>
        constructor
        . use 2; norm_num
        . use 0; norm_num
      | succ k ih =>
        obtain ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := ih
        constructor
        . use k1 + k2
          rw [pow_succ, mul_sub, mul_one, sub_add_comm, pow_succ, mul_add, mul_one, add_sub_assoc, ← sub_mul,
              Nat.cast_add, ← hk1, ← hk2]
          ring
        . use k1 * 2 + k2
          rw [pow_succ, mul_add, mul_one, pow_succ, mul_sub, mul_one, add_sub_assoc, sub_sub_eq_add_sub, ← add_mul, ← add_comm_sub,
              add_mul, mul_assoc, Real.mul_self_sqrt zero_le_two,
              Nat.cast_add, Nat.cast_mul, ← hk1, ← hk2]
          ring

    obtain ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := r31 (n)
    use k1 + k2
    rw [pow_succ (1 - √ 2), pow_succ (1 + √ 2),
      mul_sub, mul_one, sub_add_comm, mul_add, mul_one, add_sub_assoc, ← sub_mul,
      Nat.cast_add, ← hk1, ← hk2]
    ring

  -- the closed-form solution is:
  -- $$
  -- t_n = \frac{(1+\sqrt{2})^{n+1} - (1-\sqrt{2})^{n+1}}{2\sqrt{2}}
  -- $$
  have r2 : ∀ n, f n = ((1 + √ 2) ^ (n + 1) - (1 - √ 2) ^ (n + 1)) * √ 2 / 4 := by
    intro n
    have : ∀ x ≤ n, f x = ((1 + √ 2) ^ (x + 1) - (1 - √ 2) ^ (x + 1)) * √ 2 / 4 := by
      induction n with
      | zero =>
        intro x hx
        rw [Nat.eq_zero_of_le_zero hx,
            zero_add, pow_one, pow_one, ← sub_add, add_sub_cancel_left,
            ← two_mul, mul_assoc, Real.mul_self_sqrt zero_le_two, h_f0]
        norm_num
      | succ n ih =>
        intro x hx
        rcases Nat.lt_or_ge n 1 with hngt1 | hngt1
        -- n < 1 -> n = 0 -> x = 0 ∨ x = 1 -> True
        . rw [Nat.lt_one_iff.mp hngt1, zero_add] at hx
          have : x = 0 ∨ x = 1 := by exact Nat.le_one_iff_eq_zero_or_eq_one.mp hx
          rcases this with hx | hx
          . simp_all
          . rw [hx, h_f1]
            ring_nf
            rw [Real.sq_sqrt zero_le_two]
        -- n ≥ 1 -> just do some computation
        . rcases Nat.lt_or_ge x (n + 1) with hx' | hx'
          . exact ih x (Nat.le_of_lt_succ hx')
          rw [Nat.le_antisymm hx hx']
          have : f (n + 1) = 2 * f (n - 1 + 1) + f (n - 1) := by
            specialize h_fother (n - 1)
            have t1 : n - 1 + 2 = n + 1 := by
              zify; rw [Nat.cast_sub (by linarith)]; ring
            rw [t1, Nat.sub_add_cancel (by linarith)] at h_fother
            rw [Nat.sub_add_cancel (by linarith)]
            exact h_fother

          rw [this, Nat.cast_add, Nat.cast_mul,
              ih (n - 1) (Nat.sub_le n 1), ih (n - 1 + 1) (by omega)]

          -- a bunch of computation...
          norm_cast

          apply (mul_left_inj' (show (4 / √ 2) ≠ 0 by norm_num)).mp

          rw [add_mul]
          conv =>
            lhs
            enter [1]
            rw [mul_assoc, ← mul_div_assoc, div_mul_cancel₀ _ (by norm_num),
                mul_div_cancel_right₀ _ (by norm_num), Nat.sub_add_cancel hngt1,
                mul_comm, sub_mul, pow_succ, mul_assoc, pow_succ, mul_assoc]
          conv =>
            lhs
            enter [2]
            rw [← mul_div_assoc, div_mul_cancel₀ _ (by norm_num),
                mul_div_cancel_right₀ _ (by norm_num), Nat.sub_add_cancel hngt1,
                ← mul_one ((1 + √ 2) ^ n), ← mul_one ((1 - √ 2) ^ n)]
          conv =>
            rhs
            rw [← mul_div_assoc, div_mul_cancel₀ _ (by norm_num),
                mul_div_cancel_right₀ _ (by norm_num),
                pow_succ, pow_succ, mul_assoc, pow_succ, pow_succ, mul_assoc]

          have r1 : (1 + √2) * 2 + 1 = (1 + √2) * (1 + √2) := by
            rw [mul_two, mul_add, mul_one, add_mul, one_mul, Real.mul_self_sqrt zero_le_two]
            ring

          have r2 : (1 - √2) * 2 + 1 = (1 - √2) * (1 - √2) := by
            rw [mul_two, mul_sub, mul_one, sub_mul, Real.mul_self_sqrt zero_le_two]
            ring

          rw [sub_add_sub_comm, ← mul_add, ← mul_add, r1, r2]

    specialize this n
    simp_all

  -- Step 3: Expressing $ t_{2n+1} $ in Terms of $ t_n $

  have r3 : f (2 * n + 1) = f n * ((1 - √ 2) ^ (n + 1) + (1 + √ 2) ^ (n + 1)) := by
    rw [r2 (2 * n + 1), r2 n]
    apply (mul_left_inj' (show (4 / √ 2) ≠ 0 by norm_num)).mp
    conv =>
      lhs
      rw [← mul_div_assoc, div_mul_cancel₀ _ (by norm_num), mul_div_cancel_right₀ _ (by norm_num),
          show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_mul', pow_mul']
    conv =>
      rhs
      rw [mul_assoc, mul_comm _ (4 / √ 2), ← mul_assoc,
          ← mul_div_assoc, div_mul_cancel₀ _ (by norm_num), mul_div_cancel_right₀ _ (by norm_num),
          mul_add, sub_mul, sub_mul, mul_comm, ← sub_eq_sub_add_sub, ← pow_two, ← pow_two]

  -- Step 4: Conclusion

  obtain ⟨t, ht⟩ := r1
  rw [← ht] at r3
  norm_cast at r3
  rw [r3]
  exact Nat.dvd_mul_right (f n) t
