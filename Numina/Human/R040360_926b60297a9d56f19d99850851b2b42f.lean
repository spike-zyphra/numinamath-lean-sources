import Mathlib

open Finset

def S : ℕ → ℕ
| m => (Nat.digits 10 m).sum

def P : ℕ → ℕ
| m => (Nat.digits 10 m).prod

/- For a positive integer $m$ denote by $S(m)$ and $P(m)$ the sum and product, respectively, of the digits of $m$. Show that for each positive integer $n$, there exist positive integers $a_{1}, a_{2}, \ldots, a_{n}$ satisfying the following conditions:

$$
S\left(a_{1}\right)<S\left(a_{2}\right)<\cdots<S\left(a_{n}\right) \text { and } S\left(a_{i}\right)=P\left(a_{i+1}\right) \quad(i=1,2, \ldots, n)
$$

(We let $\left.a_{n+1}=a_{1}.\right)$ (Problem Committee of the Japan Mathematical Olympiad Foundation) -/
theorem number_theory_605529 (n : ℕ) (hn : 0 < n) :
    ∃ a : ℕ → ℕ,
      (∀ i < n, 0 < a i) ∧
      StrictMonoOn (fun i => S (a i)) (Ico 0 n) ∧
      ∀ i < n, S (a i) = P (a ((i + 1) % n)) := by
  exists (fun i =>
    match i with
    | .zero => Nat.ofDigits 10 (List.replicate (8 * 2^n - (4 * n + 4)) 1 ++ List.replicate (2 * n + 2) 2)
    | i + 1 => Nat.ofDigits 10 (List.replicate (2^(n + 4 + i) - 2 * (n + i + 3)) 1 ++ List.replicate (n + i + 3) 2))
  -- first we prove this inequality
  have kinq : 8 * 2^n > 4 * n + 4 := by
    clear * -
    induction n with
    | zero => decide
    | succ n hn =>
      ring_nf at hn
      ring_nf
      omega
  -- we prove Nat.ofDigits is only zero if all elements are zero
  have zz (x : List ℕ) : x.all (fun i => i = 0) ↔ Nat.ofDigits 10 x = 0 := by
    clear * -
    induction x with
    | nil => simp
    | cons head tail ih => simp_all [Nat.ofDigits]
  -- second we prove that constructed numbers are nonzero
  have nz (a b : ℕ) (h1 : a ≠ 0) (h2 : b ≠ 0) : Nat.ofDigits 10 (List.replicate a 1 ++ List.replicate b 2) ≠ 0 := by
    simp only [ne_eq, ← zz, List.all_append, List.all_replicate, one_ne_zero, decide_false,
      Bool.if_false_right, Bool.and_true, OfNat.ofNat_ne_zero, Bool.and_eq_true, decide_eq_true_eq,
      not_and]
    omega
  constructor
  · intros m1 b1
    obtain _ | m1 := m1
    · simp only
      apply Nat.pos_of_ne_zero
      apply nz
      · have := @Nat.pow_pos 2 n (by norm_num)
        omega
      · omega
    -- now we prove all numbers are positive
    simp only [Nat.add_succ_sub_one, Nat.succ_add_sub_one]
    apply Nat.pos_of_ne_zero
    apply nz
    · have u1 := @Nat.pow_pos 2 n (by norm_num)
      have u2 := @Nat.pow_pos 2 m1 (by norm_num)
      simp only [Nat.pow_add]
      have stp : 2 ^ n * 16 > 8 * n + 8 := by linarith
      have ty := Nat.pow_lt_pow_right (a := 2) (by norm_num) b1
      rw [Nat.pow_add] at ty
      norm_num at ty
      rw [(by norm_num : 2^4 = 16)]
      rw [← Nat.pos_iff_ne_zero]
      have mg : 2 ^ n * 16 ≤ 2 ^ n * 16 * 2 ^ m1 := by
        conv =>
          left
          rw [← mul_one (2 ^ n * 16)]
        apply Nat.mul_le_mul_left
        linarith
      omega
    · linarith
  constructor
  -- now we prove that the function is monotonic
  · intros m1 b1 m2 b2 hm
    obtain _ | m1 := m1
    -- m1 zero, m2 nonzero
    · obtain _ | m2 := m2
      · norm_num at hm
      simp only [S, Nat.reduceLeDiff]
      rw [Nat.digits_ofDigits _ (by norm_num)]
      rw [Nat.digits_ofDigits _ (by norm_num)]
      -- sum
      · simp only [List.sum_append, List.sum_replicate, smul_eq_mul, mul_one, Nat.pow_add]
        rw [(by omega : 8 * 2 ^ n - (4 * n + 4) + (2 * n + 2) * 2 = 8 * 2^n)]
        have u2 := @Nat.pow_pos 2 m2 (by norm_num)
        have ii := @Nat.pow_pos 2 n (by norm_num)
        have mg : 2 ^ n * 16 ≤ 2 ^ n * 16 * 2 ^ m2 := by
          conv =>
            left
            rw [← mul_one (2 ^ n * 16)]
          apply Nat.mul_le_mul_left
          linarith
        simp only [Nat.Ico_zero_eq_range, coe_range, Set.mem_Iio] at b1 b2
        suffices 8 * 2 ^ n < 2 ^ n * 2 ^ 4 * 2 ^ m2 by omega
        rw [show 2 ^ 4 = 16 by norm_num]
        suffices 8 * 2 ^ n < 2 ^ n * 16 * 2 ^ m2 by linarith
        nlinarith [mg, show 0 < 2 ^ m2 by positivity, show 0 < 2 ^ n by positivity]
      · simp only [List.mem_append, List.mem_replicate, ne_eq, AddLeftCancelMonoid.add_eq_zero,
        OfNat.ofNat_ne_zero, and_false, not_false_eq_true, true_and]
        simp only [Nat.Ico_zero_eq_range, coe_range, Set.mem_Iio] at b1 b2
        -- now we prove all digits are less than 10
        intro l h
        rcases h with h₁ | h₂
        · -- Case where ¬2^(n+4+m2) - 2*(n+m2+3) = 0 ∧ l = 1
          rcases h₁ with ⟨h₃, h₄⟩
          rw [h₄]
          trivial
        · -- Case where l = 2
          rw [h₂]
          trivial
      -- side conditions
      · simp
      · simp only [List.mem_append, List.mem_replicate, ne_eq, AddLeftCancelMonoid.add_eq_zero,
        mul_eq_zero, OfNat.ofNat_ne_zero, false_or, and_false, not_false_eq_true, true_and]
        omega
      · simp
    -- m2 is forced to be nonzero
    · obtain _ | m2 := m2
      · norm_num at hm
      simp only [S, Nat.reduceLeDiff]
      rw [Nat.digits_ofDigits _ (by norm_num) _ (by simp only [List.mem_append, List.mem_replicate,
        ne_eq, AddLeftCancelMonoid.add_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, one_ne_zero,
        and_false, and_self, or_self, not_false_eq_true, true_and]; omega) (by simp)]
      rw [Nat.digits_ofDigits _ (by norm_num) _ (by simp only [List.mem_append, List.mem_replicate,
        ne_eq, AddLeftCancelMonoid.add_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, one_ne_zero,
        and_false, and_self, or_self, not_false_eq_true, true_and]; omega) (by simp)]
      simp only [Nat.Ico_zero_eq_range, coe_range, Set.mem_Iio] at b1 b2
      -- turn into arithmetic
      simp only [List.sum_append, List.sum_replicate, smul_eq_mul, mul_one]
      have h1 : m1 < m2 := by omega
      have h2 : n + 4 + m1 < n + 4 + m2 := by omega
      have h3 : 2 ^ (n + 4 + m1) < 2 ^ (n + 4 + m2) := by 
        apply Nat.pow_lt_pow_right
        all_goals omega
      omega
  -- we prove the final property, which is quite difficult
  · intros i hi
    obtain _ | i := i
    · simp only [S, Nat.reduceLeDiff, P, zero_add]
      clear zz nz
      obtain _ | n := n
      · norm_num at hi
      obtain _ | n := n
      · simp only [zero_add, pow_one, Nat.reduceMul, mul_one, Nat.reduceAdd, Nat.reduceSub,
        List.reduceReplicate, List.cons_append, List.singleton_append, Nat.reduceLeDiff]
        native_decide
      simp only [Nat.reduceLeDiff, Nat.one_mod, add_zero]
      rw [Nat.digits_ofDigits _ (by norm_num) _ (by simp only [List.mem_append, List.mem_replicate,
        ne_eq, AddLeftCancelMonoid.add_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, one_ne_zero,
        and_false, and_self, or_self, not_false_eq_true, true_and]; omega)]
      rw [Nat.digits_ofDigits _ (by norm_num) _ (by simp only [List.mem_append, List.mem_replicate,
        ne_eq, AddLeftCancelMonoid.add_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, one_ne_zero,
        and_false, and_self, or_self, not_false_eq_true, true_and]; omega)]
      -- we have List.replicate, now it's time to turn into arithmetic 
      simp only [List.sum_append, List.sum_replicate, smul_eq_mul, mul_one, List.prod_append,
        List.prod_replicate, one_pow, one_mul]
      -- now we use AI to solve
      ring_nf; omega
      · simp only [ne_eq, List.append_eq_nil, List.replicate_eq_nil_iff,
        List.replicate_succ_ne_nil, and_false, not_false_eq_true, List.getLast_append_of_ne_nil,
        List.getLast_replicate, OfNat.ofNat_ne_zero, imp_self]
        simp only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, and_self,
          OfNat.ofNat_ne_zero, not_false_eq_true, ne_eq, List.replicate_succ_ne_nil,
          List.getLast_append_of_ne_nil, List.getLast_replicate, imp_self]
      · simp only [ne_eq,
          List.append_eq_nil, List.replicate_eq_nil_iff, List.replicate_succ_ne_nil, and_false,
          not_false_eq_true, List.getLast_append_of_ne_nil, List.getLast_replicate,
          OfNat.ofNat_ne_zero, imp_self]
        simp_rw [List.getLast_append]
        simp only [AddLeftCancelMonoid.add_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, one_ne_zero,
          and_false, and_self, or_self, not_false_eq_true, List.isEmpty_replicate, decide_false,
          Bool.false_eq_true, ↓reduceDIte, List.getLast_replicate, imp_self]
    -- now let's check for the case where i > 0
    simp only [S, Nat.reduceLeDiff, P]
    obtain rfl | jj : n = i + 1 + 1 ∨ i + 1 + 1 < n := by omega
    -- when n = i + 1 + 1
    · simp only [Nat.reduceLeDiff, Nat.mod_self]
      rw [Nat.digits_ofDigits _ (by norm_num) _ (by simp only [List.mem_append, List.mem_replicate,
        ne_eq, AddLeftCancelMonoid.add_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, one_ne_zero,
        and_false, and_self, or_self, not_false_eq_true, true_and]; omega) (by simp)]
      rw [Nat.digits_ofDigits _ (by norm_num) _ (by simp only [List.mem_append, List.mem_replicate,
        ne_eq, AddLeftCancelMonoid.add_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, one_ne_zero,
        and_false, and_self, or_self, not_false_eq_true, true_and]; omega) (by simp)]
      -- now turn into arithmetic
      simp only [List.sum_append, List.sum_replicate, smul_eq_mul, mul_one, List.prod_append,
        List.prod_replicate, one_pow, one_mul]
      -- now turn into integers
      have md : 2 ^ (i + 1 + 1 + 4 + i) >= 2 * (i + 1 + 1 + i + 3) := by
        have h1 : 2 ^ (i + 1 + 1 + 4 + i) = 2 ^ (2 * i + 6) := by ring_nf
        have h4 : 2 * (i + 1 + 1 + i + 3) = 4 * i + 10 := by ring
        rw [h1, h4]
        have h5 : ∀ i : ℕ, 2 ^ (2 * i + 6) ≥ 4 * i + 10 := by
          intro i
          induction i with
          | zero =>
            norm_num
          | succ i ih =>
            have h1 : 2 ^ (2 * (i + 1) + 6) = 2 ^ (2 * i + 6) * 4 := by
              ring_nf
            rw [h1]
            have h2 : 2 ^ (2 * i + 6) ≥ 4 * i + 10 := ih
            omega
        specialize h5 i
        linarith
      -- now finish the goal using AI
      zify [md]
      ring
    · rw [Nat.mod_eq_of_lt jj]
      simp only [Nat.reduceLeDiff]
      -- remove digits (ofDigits _)
      rw [Nat.digits_ofDigits _ (by norm_num) _ (by simp only [List.mem_append, List.mem_replicate,
        ne_eq, AddLeftCancelMonoid.add_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, one_ne_zero,
        and_false, and_self, or_self, not_false_eq_true, true_and]; omega) (by simp)]
      rw [Nat.digits_ofDigits _ (by norm_num) _ (by simp only [List.mem_append, List.mem_replicate,
        ne_eq, AddLeftCancelMonoid.add_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, one_ne_zero,
        and_false, and_self, or_self, not_false_eq_true, true_and]; omega) (by simp)]
      -- turn into arithmetic
      simp only [List.sum_append, List.sum_replicate, smul_eq_mul, mul_one, List.prod_append,
        List.prod_replicate, one_pow, one_mul]
      simp only [Nat.pow_add, Nat.reducePow, pow_one]
      -- turn into integers
      have rt : 2 ^ n * 16 * 2 ^ i ≥ 2 * (n + i + 3) := by
        have h1 : 2 ^ n * 16 * 2 ^ i = 2 * 2 ^ (n + i + 3) := by
          ring_nf

        rw [h1]

        have h3 : n + i + 3 > 0 := by 
          have h4 : n > 0 := by linarith
          have h5 : i ≥ 0 := by omega
          omega

        have h4 : 2 ^ (n + i + 3) ≥ n + i + 3 := by 
          have h5 : ∀ k, k > 0 → 2 ^ k ≥ k := by
            intro k hk
            have h6 : k ≥ 1 := by linarith
            have h : ∀ m, 2 ^ (m + 1) ≥ m + 1 := by
              intro m
              induction m with
              | zero =>
                simp
              | succ m ih =>
                simp [pow_succ] at ih ⊢
                linarith [ih]
            have hk' : k - 1 ≥ 0 := by omega
            have h7 : 2 ^ ((k - 1) + 1) ≥ (k - 1) + 1 := h (k - 1)
            have h8 : k = (k - 1) + 1 := by omega
            rw [h8]
            linarith
          specialize h5 (n + i + 3) h3
          exact h5

        linarith [h4]
      zify [rt]
      ring