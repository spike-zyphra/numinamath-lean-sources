import Mathlib

/- Determine all positive integers $n$ for which the equation

$$
x^{n}+(2+x)^{n}+(2-x)^{n}=0
$$

has an integer as a solution.

## Answer: $n=1$. -/
theorem algebra_604531 (n : ℕ) (hn : n > 0):
    (∃ x : ℤ, x^n + (2 + x)^n + (2 - x)^n = 0) ↔ n = 1 := by

    -- We start by proving a bunch of lemmas.

    -- 1. a ≡ -a (mod 2)
    have neg_mod_two (a : ℤ) : a ≡ -a [ZMOD 2] := by
      have : -a = (-1) * a := by exact Int.neg_eq_neg_one_mul a
      rw [this]
      have : a = 1 * a := by exact Eq.symm (Int.one_mul a)
      nth_rw 1 [this]
      have : 1 ≡ -1 [ZMOD 2] := by rfl
      exact Int.ModEq.mul this rfl

    -- 2. powers of odd number remains odd
    have odd_pow_odd {a : ℤ} (n : ℕ) (ha : a ≡ 1 [ZMOD 2]) :
      a ^ n ≡ 1 [ZMOD 2] := by
      induction n
      case zero => simp [ha]
      case succ n ih =>
        rw [pow_succ]
        calc
          a ^ n * a ≡ a ^ n * 1 [ZMOD 2] := by apply Int.ModEq.mul_left; assumption
          _ ≡ 1 * 1 [ZMOD 2] := by simp [ih]

    -- 3. powers of even number remains even
    have even_pow_even {a : ℤ} (n : ℕ) (hn : n ≠ 0) (ha : a ≡ 0 [ZMOD 2]) :
      a ^ n ≡ 0 [ZMOD 2] := by
      unfold Int.ModEq at ha ⊢
      simp_all
      exact Dvd.dvd.pow ha hn

    -- 4. for odd n, we have a ^ n + b ^ n = (a + b) * (a^(n-1) - a^(n-2)*b + ... + b^(n-1))
    have odd_pow_add (a b : ℤ) {n : ℕ} (hn : Odd n) :
      a ^ n + b ^ n = (a + b) * ∑ i ∈ Finset.range n, (-1) ^ i * a ^ i * b ^ (n - 1 - i) := by

      -- from the fact that n is odd, we deduce: n > 0 and n = (n - 1) + 1
      have npos : n > 0 := by exact Odd.pos hn
      have n_eq : n = (n - 1) + 1 := by exact (Nat.sub_eq_iff_eq_add npos).mp rfl
      have minus_one_eq : (-1) ^ (n - 1) = 1 := by
        apply Even.neg_one_pow
        apply Nat.Odd.sub_odd hn
        norm_num

      -- we start by putting (a + b) into the sum
      rw [add_mul, Finset.mul_sum, Finset.mul_sum]

      -- in the second sum ∑ i ∈ Finset.range n, b * ((-1) ^ i * a ^ i * b ^ (n - 1 - i)),
      -- we take out the first summand, which will be shown to be b ^ n
      nth_rw 2 [Finset.sum_range_eq_add_Ico]
      case hn => exact npos
      simp
      have : b * b ^ (n - 1) = b ^ n := by
        nth_rw 1 [← pow_one b]
        rw [← pow_add]
        congr
        exact Nat.add_sub_of_le npos
      rw [this]

      -- in the first sum ∑ i ∈ Finset.range n, a * ((-1) ^ i * a ^ i * b ^ (n - 1 - i)),
      -- we take out the last summand, which will be shown to be a ^ n
      nth_rw 3 [n_eq]
      rw [Finset.sum_range_succ]
      simp [minus_one_eq]
      have : a * a ^ (n - 1) = a ^ n := by
        nth_rw 1 [← pow_one a]
        rw [← pow_add]
        congr
        exact Nat.add_sub_of_le npos
      rw [this]

      -- reformulate the sums, to group together (a ^ n + b ^ n)
      rw [show Finset.range (n - 1) = Finset.Ico 0 (n - 1) by simp [npos]]
      rw [add_assoc]
      nth_rw 2 [add_comm]
      rw [← add_assoc]
      nth_rw 1 [add_assoc]

      -- then it suffices to prove the remaining sum equals zero
      suffices h : ∑ x ∈ Finset.Ico 1 n, b * ((-1) ^ x * a ^ x * b ^ (n - 1 - x)) + ∑ x ∈ Finset.Ico 0 (n - 1), a * ((-1) ^ x * a ^ x * b ^ (n - 1 - x)) = 0 by rw [h]; ring

      -- change the summing index of the second sum, so it ranges from 1 to n-1, to match the first sum
      have : ∑ x ∈ Finset.Ico 0 (n - 1), a * ((-1) ^ x * a ^ x * b ^ (n - 1 - x)) = ∑ x ∈ Finset.Ico 0 (n - 1), a * ((-1) ^ (1 + x - 1) * a ^ (1 + x - 1) * b ^ (n - 1 - (1 + x - 1))) := by simp
      rw [this]
      rw [Finset.sum_Ico_add (fun x ↦ a * ((-1) ^ (x - 1) * a ^ (x - 1) * b ^ (n - 1 - (x - 1)))) 0 (n-1) 1]
      simp
      rw [← n_eq]

      -- now the two sums can be merged
      rw [← Finset.sum_add_distrib]

      -- and we prove it sums to zero by showing each summand equals zero
      apply Finset.sum_eq_zero
      intro i hi
      obtain ⟨hi₁, hi₂⟩ := Finset.mem_Ico.mp hi

      -- reformulate the formula, grouping powers of b together
      have : b * ((-1) ^ i * a ^ i * b ^ (n - 1 - i)) = (-1) ^ i * (a ^ i * (b * b ^ (n - 1 - i))) := by ring
      rw [this]
      have : b * b ^ (n - 1 - i) = b ^ (n - i) := by
        nth_rw 1 [← pow_one b]
        rw [← pow_add]
        congr
        have : n - i = 1 + ((n - i) - 1) := by
          apply Eq.symm
          apply Nat.add_sub_cancel'
          exact Nat.le_sub_of_add_le' hi₂
        rw [this]
        congr 1
        exact Nat.sub_right_comm n 1 i
      rw [this]

      have : n - 1 - (i - 1) = n - i := Nat.sub_sub_sub_cancel_right hi₁
      rw [this]

      -- reformulate the formula, group powers of a together
      have : a * ((-1) ^ (i - 1) * a ^ (i - 1) * b ^ (n - i)) = (-1) ^ (i - 1) * (a * a ^ (i - 1) * b ^ (n - i)) := by ring
      rw [this]
      have : a * a ^ (i - 1) = a ^ i := by
        nth_rw 1 [← pow_one a]
        rw [← pow_add]
        congr
        exact Nat.add_sub_of_le hi₁
      rw [this]

      -- extract common factor
      rw [← add_mul]
      -- it turns out we only need to prove the following
      suffices h : ((-1) ^ i + (-1) ^ (i - 1)) = 0 by rw [h]; simp

      -- this is proved by a simple case analysis on whether i is odd or even
      rcases Nat.even_or_odd i with h_even | h_odd
      · have : Odd (i - 1) := by apply Nat.Even.sub_odd hi₁ h_even; norm_num
        rw [Even.neg_one_pow h_even, Odd.neg_one_pow this]
        simp
      · have : Even (i - 1) := by apply Nat.Odd.sub_odd h_odd; norm_num
        rw [Odd.neg_one_pow h_odd, Even.neg_one_pow this]
        simp

    -- With the above lemmas, we now start proving the theorem
    constructor
    · -- necessity, we show by contradiction
      by_contra! h
      obtain ⟨⟨x, hx⟩, nne⟩ := h  -- assuming the equation has a integer solution x when n ≠ 1

      -- do case analysis on whether n is even or odd
      rcases Nat.even_or_odd n with neven | nodd
      · -- In case n is even, the 3 terms x ^ n, (2 + x) ^ n, (2 - x) ^ n
        -- are all non-negative, and at least one of them is positive, so
        -- their sum cannot be equal to zero.
        have : x ^ n ≥ 0 := by exact Even.pow_nonneg neven x
        by_cases h : 2 + x = 0
        · have : (2 + x) ^ n ≥ 0 := by exact Even.pow_nonneg neven (2 + x)
          have : 2 - x ≠ 0 := by linarith
          have : (2 - x) ^ n > 0 := by apply Even.pow_pos neven this
          linarith
        · have : (2 - x) ^ n ≥ 0 := by exact Even.pow_nonneg neven (2 - x)
          have : (2 + x) ^ n > 0 := by apply Even.pow_pos neven h
          linarith
      · -- The case n is odd is trickier
        -- as n is odd, and n ≠ 1, we must have n ≥ 2
        have n_ge_2 : n ≥ 2 := by
          apply (Nat.two_le_iff n).mpr
          constructor
          · linarith
          exact nne

        -- we exhibit the equation modulo 2
        have h_eq_mod_2 : x ^ n + (2 + x) ^ n + (2 - x) ^ n ≡ 0 [ZMOD 2] := by
          exact congrFun (congrArg HMod.hMod hx) 2

        -- from this we show by contradiction that x must be even
        have h_x_even : Even x := by
          by_contra! h
          -- otherwise, x is odd, then 2 + x and 2 - x are all odd
          have h' : Odd x := by exact Int.not_even_iff_odd.mp h
          have h₁ : x ≡ 1 [ZMOD 2] := Int.odd_iff.mp h'
          have h₂ : 2 + x ≡ 1 [ZMOD 2] := by
            calc
              2 + x ≡ 2 + 1 [ZMOD 2] := by apply Int.ModEq.add_left; exact h₁
              _ ≡ 1 [ZMOD 2] := by rfl
          have h₃ : 2 - x ≡ 1 [ZMOD 2] := by
            calc
              2 - x ≡ 2 - 1 [ZMOD 2] := by apply Int.ModEq.sub_left; exact h₁
              _ ≡ 1 [ZMOD 2] := by rfl
          unfold Int.ModEq at h_eq_mod_2
          -- so the powers of x, 2 + x, 2 - x remains odd
          have h₁' := odd_pow_odd n h₁
          have h₂' := odd_pow_odd n h₂
          have h₃' := odd_pow_odd n h₃
          -- we derive a contradiction from that 3 odd numbers cannot sum to an even number
          rw [
            Int.ModEq.add_left (x ^ n + (2 + x) ^ n) h₃',
            add_assoc,
            Int.ModEq.add_right (((2 + x) ^ n + 1)) h₁',
            add_comm,
            add_assoc,
            Int.ModEq.add_right (1 + 1) h₂'
          ] at h_eq_mod_2
          simp at h_eq_mod_2

        -- now that we show x is even, we can write x = 2 * y for some y
        obtain ⟨y, rfl⟩ := h_x_even
        -- reformulate the equation to get 2 ^ n * (y ^ n + (1 + y) ^ n + (1 - y) ^ n) = 0
        rw [(show y + y = 2 * y by ring), mul_pow] at hx
        have : 2 + 2 * y = 2 * (1 + y) := by ring
        rw [this] at hx
        have : 2 - 2 * y = 2 * (1 - y) := by ring
        rw [this] at hx
        rw [mul_pow, mul_pow] at hx
        have : 2 ^ n * y ^ n + 2 ^ n * (1 + y) ^ n + 2 ^ n * (1 - y) ^ n = 2 ^ n * (y ^ n + (1 + y) ^ n + (1 - y) ^ n) := by ring
        rw [this] at hx
        -- so the number y satisfies the equation y ^ n + (1 + y) ^ n + (1 - y) ^ n = 0
        have hy : y ^ n + (1 + y) ^ n + (1 - y) ^ n = 0 := by simp_all

        -- conduct a parity analysis on y similar to the above, and we derive that y must be even.
        have h_eq_mod_2' : y ^ n + (1 + y) ^ n + (1 - y) ^ n ≡ 0 [ZMOD 2] := by exact congrFun (congrArg HMod.hMod hy) 2
        have h_y_even : Even y := by
          by_contra! h
          have h' : Odd y := by exact Int.not_even_iff_odd.mp h
          have h₁ : y ≡ 1 [ZMOD 2] := Int.odd_iff.mp h'
          have h₂ : 1 + y ≡ 0 [ZMOD 2] := by
            calc
              1 + y ≡ 1 + 1 [ZMOD 2] := by apply Int.ModEq.add_left; exact h₁
              _ ≡ 0 [ZMOD 2] := by rfl
          have h₃ : 1 - y ≡ 0 [ZMOD 2] := by
            calc
              1 - y ≡ 1 - 1 [ZMOD 2] := by apply Int.ModEq.sub_left; exact h₁
              _ ≡ 0 [ZMOD 2] := by rfl
          have h₁' := odd_pow_odd n h₁
          have h₂' := even_pow_even n (show n ≠ 0 by linarith) h₂
          have h₃' := even_pow_even n (show n ≠ 0 by linarith) h₃
          unfold Int.ModEq at h_eq_mod_2'
          rw [
            Int.ModEq.add_left (y ^ n + (1 + y) ^ n) h₃',
            add_zero,
            Int.ModEq.add_left (y ^ n) h₂',
            add_zero,
            h₁'
          ] at h_eq_mod_2'
          contradiction

        -- now we use the formula for a ^ n + b ^ n to reformulate the sum (1 + y) ^ n + (1 + y) ^ n
        rw [add_assoc, odd_pow_add _ _ nodd, show 1 + y + (1 - y) = 2 by ring] at hy
        -- we get that y ^ n = -2 * ∑ i ∈ [0, n - 1], (-1) ^ i * (1 + y) ^ i * (1 - y) ^ (n - 1 - i)
        have y_to_n := add_eq_zero_iff_eq_neg.mp hy
        rw [← neg_mul] at y_to_n

        -- first, we show y ^ n / (-2) =  ∑ i ∈ [0, n - 1], (-1) ^ i * (1 + y) ^ i * (1 - y) ^ (n - 1 - i) is and odd number
        have h_sum_mod_2 : (∑ i ∈ Finset.range n, (-1) ^ i * (1 + y) ^ i * (1 - y) ^ (n - 1 - i)) % 2 = 1 := by
          rw [Finset.sum_int_mod]
          -- every summand equals to 1 modulo 2
          have : ∑ i ∈ Finset.range n, (-1) ^ i * (1 + y) ^ i * (1 - y) ^ (n - 1 - i) % 2 = ∑ i ∈ Finset.range n, 1 := by
            apply eq_of_sub_eq_zero
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_eq_zero
            rintro i _
            apply sub_eq_zero.mpr
            suffices h : Odd ((-1) ^ i * (1 + y) ^ i * (1 - y) ^ (n - 1 - i)) by exact Int.odd_iff.mp h
            apply Int.odd_mul.mpr
            constructor
            · apply Int.odd_mul.mpr
              constructor
              · exact Int.odd_iff.mpr (odd_pow_odd i (neg_mod_two (-1)))
              refine Odd.pow ?h.h.left.right.ha
              exact Even.one_add h_y_even
            refine Odd.pow ?h.h.right.ha
            refine Int.odd_sub.mpr ?h.h.right.ha.a
            simp [h_y_even]
          rw [this]
          -- so the sum is n * 1 = n
          rw [Finset.sum_eq_card_nsmul (show ∀ i ∈ Finset.range n, (1 : ℤ) = 1 by simp)]
          simp
          norm_cast
          -- recall n is odd, we are done
          exact Nat.odd_iff.mp nodd

        -- second, we show y ^ n is a multiple of 4, as y is a multiple of 2 and n ≥ 2
        have : y ^ n % 4 = 0 := by
          simp
          obtain ⟨t, rfl⟩ := h_y_even
          rw [← two_mul, mul_pow]
          have : (4 : ℤ) ∣ 2 ^ n := by
            have : n = 2 + (n - 2) := by exact Eq.symm (Nat.add_sub_of_le n_ge_2)
            rw [this, pow_add, show (2 ^ 2 : ℤ) = 4 by rfl]
            simp
          exact Dvd.dvd.mul_right this (t ^ n)
        rw [y_to_n] at this

        -- a small lemma, from which we deduce
        -- y ^ n / (-2) = ∑ i ∈ [0, n - 1], (-1) ^ i * (1 + y) ^ i * (1 - y) ^ (n - 1 - i)
        -- must be even
        have mod_4 (x : ℤ) : (-2 * x) % 4 = 0 ↔ x % 2 = 0 := by
          constructor
          · simp
            intro hx
            obtain ⟨t, ht⟩ := hx
            have : x = 2 * t := by linarith
            rw [this]
            simp
          · intro hx
            simp at hx ⊢
            obtain ⟨t, rfl⟩ := hx
            rw [← mul_assoc]
            simp

        -- thus we deduce a contradiction
        rw [mod_4 _, h_sum_mod_2] at this
        contradiction
    · -- for sufficiency, we just show that x = -4 is a solution for n = 1
      intro neq1
      rw [neq1]
      use -4
      norm_num
