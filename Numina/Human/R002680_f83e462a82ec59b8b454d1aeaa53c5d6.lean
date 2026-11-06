import Mathlib.Tactic

/-
Let $m, n \geq 1$ be integers. Show that $3^{m}+3^{n}+1$ is not a perfect
square.
-/
theorem number_theory_99705 (m n : ℕ) (pos_m : 0 < m) (pos_n : 0 < n) :
    ¬∃ k, k^2 = 3^m + 3^n + 1 := by
  simp
  intro r
  -- First show r^2 is either 0, 1 or 4 mod 8
  have : r^2 ≡ 0 [MOD 8] ∨ r^2 ≡ 1 [MOD 8] ∨ r^2 ≡ 4 [MOD 8] := by
    -- r is either even or odd, so ∃k s.t. r = 2k or r = 2k + 1
    obtain ⟨ k, or ⟩ := Nat.even_or_odd' r
    -- Rewrite mod 8 as 8 divides
    cases or <;> simp_all only
      <;> norm_num [mul_pow, Nat.modEq_iff_dvd]
      -- k is either even or odd, so ∃l s.t. k = 2l or k = 2l + 1
      <;> obtain ⟨ l, or_r ⟩ := Nat.even_or_odd' k
      -- Rewrite everything in terms of l, and convert to ints
      <;> cases or_r <;> simp_all only <;> zify
    -- Handle each case by factoring out 8
    · apply Or.inl
      convert_to (8 : ℤ) ∣ 8 * (2 * l^2)
      · ring
      norm_num
    · apply Or.inr; apply Or.inr
      convert_to (8 : ℤ) ∣ 8 * (-(2 * l) - (2 * l^2))
      · ring
      norm_num
    · apply Or.inr; apply Or.inl
      convert_to (8 : ℤ) ∣ 8 * ((-l) - (2 * l^2))
      · ring
      norm_num
    · apply Or.inr; apply Or.inl
      convert_to (8 : ℤ) ∣ 8 * -(1 + 3 * l + (2 * l^2))
      · ring
      norm_num

  -- Then show 3^m + 3^n + 1 is either 3, 5 or 7 mod 8.
  have :
    3^m + 3^n + 1 ≡ 3 [MOD 8] ∨
    3^m + 3^n + 1 ≡ 5 [MOD 8] ∨
    3^m + 3^n + 1 ≡ 7 [MOD 8]
      := by
    -- First show that for some n, 3^n is either 1 or 3 mod 8
    have {n : ℕ} : 3 ^ n ≡ 1 [MOD 8] ∨ 3 ^ n ≡ 3 [MOD 8] := by
      -- Case split on even or odd n
      obtain ⟨ k, (even | odd) ⟩ := Nat.even_or_odd' n
      -- Arrange terms to fit congruence of powers
      · subst even -- substitute n for k
        apply Or.inl -- choose left side of goal
        norm_num [pow_mul]
        rw [<- one_pow k]
        exact Nat.ModEq.pow k rfl -- apply congruence of powers
      -- Arrange terms to fit the congruence of powers and products
      · subst odd -- substitute n for k
        apply Or.inr -- choose right side of goal
        ring_nf
        norm_num [npow_mul', @sq]
        rw [mul_comm, show 3 = 3 * 1 by rfl]
        -- Cancel a factor of 3 by the congruence of products
        apply Nat.ModEq.mul_left 3
        rw [show 1 = 1 ^ k by norm_num]
        exact Nat.ModEq.pow k rfl -- apply congruence of powers
    -- Define a helper lemma to help simplify each combination of the previous
    -- lemma applied to m and n
    have add_left_iff_sub_right { k r  : ℕ} (r_le_k : r ≤ k) :
      (3^m + 3^n) + r ≡ k [MOD 8] ↔ (3^m + 3^n) ≡ (k - r) [MOD 8] := by
        constructor
        -- Move r to the right side
        · convert Nat.ModEq.add_right_cancel' r
          norm_num [r_le_k]
        -- Move r to the left side
        · convert Nat.ModEq.add_right r
          norm_num [r_le_k]
    -- Consider all possible combinations of modular congruence for 3 ^ n and
    -- 3 ^ m
    cases @this m <;> cases @this n <;> norm_num [
      add_left_iff_sub_right
    ]
    -- Put each equation into the form a + b ≡ c + d [mod x]
    <;> rw [
      show 2 = 1 + 1 by rfl,
      show 4 = 3 + 1 by rfl,
      show 6 = 3 + 3 by rfl,
    ]
    -- Apply the congruent sum rule and simplify
    any_goals simp_all only [Nat.ModEq.add]; simp
    -- Repeat the above step to solve the remaining symmetrical case of 1 + 3
    · simp_all only [add_comm, Nat.ModEq.add]; simp

  -- These two propositions are a contradiction, because r^2 cannot
  -- have two different remainders when divided by 8.
  by_contra eq
  simp_all [Nat.modEq_iff_dvd]
  omega