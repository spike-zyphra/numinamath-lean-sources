import Mathlib

/- Example 7 Let the elements of set $A$ all be positive integers, satisfying the following conditions:
(1) The number of elements in $A$ is no less than 3;
(2) If $a \in A$, then all divisors of $a$ belong to $A$;
(3) If $a \in A, b \in A, 1< a < b$, then $1+ab \in A$.

Prove: $A=\mathbf{N}^{*}$. -/
theorem number_theory_169624 (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (hA1 : A.encard ≥ 3)
    (hA2 : ∀ a ∈ A, ∀ d ∈ Nat.divisors a, d ∈ A)
    (hA3 : ∀ a ∈ A, ∀ b ∈ A, 1 < a ∧ a < b → 1 + a * b ∈ A) :
    A = {x | 0 < x} := by
    -- From condition (hA), 0 cannot be in A since all elements are positive.
    have h0 : 0 ∉ A := by
      by_contra h
      linarith [hA 0 h]
    -- A helper lemma reinforcing that any element 'a' in A is non-zero.
    have h0' : ∀ a ∈ A, a ≠ 0 := by
      intro a ha
      by_contra h
      simp [h] at ha
      exact h0 ha
    -- Show that A is not an empty set, using condition (hA1) that its size is at least 3.
    have hA_nonempty : A.Nonempty := by
      rw [← Set.encard_pos]
      apply lt_of_lt_of_le (by norm_num) hA1
    -- Prove that 1 must be in A. Since A is non-empty, it has some element 'a'. By condition (hA2), all divisors of 'a' are in A, and 1 is a divisor of any integer.
    have h1 : 1 ∈ A := by
      let a := hA_nonempty.choose
      have ha : a ≠ 0 := by
        by_contra h
        exact h0 (by simp [← h, a, hA_nonempty.choose_spec])
      exact hA2 a (by simp [hA_nonempty.choose_spec]) 1 (by rwa [Nat.one_mem_divisors])
    -- Any element in A that is not 1 must be greater than 1, as they are all positive integers.
    have h10 : ∀ a ∈ A, a ≠ 1 → a > 1 := by
      intro a ha h1
      by_contra h
      replace h : a = 0 := by omega
      simp [h] at ha
      exact h0 ha
    -- Prove that there must exist at least two distinct elements in A that are both greater than 1. This follows from |A| ≥ 3 and 1 ∈ A.
    have hexist : ∃ a b, a > b ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ∈ A ∧ b ∈ A := by
      suffices ∃ t, t ⊆ A ∧ t.encard = 2 ∧ 1 ∉ t by
        obtain ⟨t, ⟨ht1, ht2, ht3⟩⟩ := this
        rw [Set.encard_eq_two] at ht2
        obtain ⟨x, y, hx, hy, h_distinct⟩ := ht2
        by_cases hxy : y < x
        · use x, y
          simp_all
          exact ⟨Ne.symm ht3.1, Ne.symm ht3.2, ht1 (show x ∈ {x, y} by simp),
              ht1 (show y ∈ {x, y} by simp)⟩
        · replace hxy : x < y := by omega
          use y, x
          simp_all
          exact ⟨Ne.symm ht3.2, Ne.symm ht3.1, ht1 (show y ∈ {x, y} by simp),
            ht1 (show x ∈ {x, y} by simp)⟩
      have : (A \ {1}).encard ≥ 2 := by
        rw [Set.encard_diff_singleton_of_mem h1]
        simp
        apply ENat.le_sub_of_add_le_left _ (by norm_num [hA1])
        exact ENat.one_ne_top
      have ⟨t, ht, ht1⟩ := Set.exists_subset_encard_eq this
      use t
      refine ⟨Set.subset_diff.1 ht |>.1, ht1, ?_⟩
      intro h1t
      specialize ht h1t
      simp at ht
    -- From the existence proof, we can now use two such elements, 'a' and 'b'.
    obtain ⟨a, b, hab, ha1, hb1, ha, hb⟩ := hexist
    -- Show that the larger element, 'a', must be greater than 2.
    have ha' : a > 2 := by
      specialize h10 b hb hb1
      omega
    -- Prove that 2 must be in A. This is done by contradiction. If 2 is not in A, then all elements of A must be odd (otherwise 2 would be a divisor). But if 'a' and 'b' are odd, then by (hA3), 1 + a*b is in A, which is an even number, a contradiction.
    have h2 : 2 ∈ A := by
      by_contra! h
      have h_odd : ∀ a ∈ A, Odd a := by
        intro a ha
        by_contra h_odd
        simp at h_odd
        exact h (hA2 a ha 2 (by simp [Nat.mem_divisors, Even.two_dvd h_odd]; exact h0' a ha))
      by_cases hab_lt : a < b
      · specialize hA3 a ha b hb ⟨h10 a ha ha1, hab_lt⟩
        suffices ¬ Odd (1 + a * b) by
          exact this (h_odd (1 + a * b) hA3)
        simp
        suffices Odd (a * b) by exact Odd.one_add this
        exact Odd.mul (h_odd a ha) (h_odd b hb)
      · specialize hA3 b hb a ha ⟨h10 b hb hb1, by omega⟩
        suffices ¬ Odd (1 + b * a) by
          exact this (h_odd (1 + b * a) hA3)
        simp
        suffices Odd (b * a) by exact Odd.one_add this
        exact Odd.mul (h_odd b hb) (h_odd a ha)
    -- A helper lemma to generate a specific large number in A using elements we know are in A (like 2). This shows that for any x > 2 in A, a particular quadratic in x is also in A.
    have h3 : ∀ a > 2, a ∈ A → 4 + 10 * a + 8 * a ^ 2 ∈ A := by
      intro x hx hxA
      have h31 : 1 + 2 * x ∈ A := hA3 2 h2 x hxA (by omega)
      have h32 : 3 + 4 * x ∈ A := by
        specialize hA3 2 h2 (1 + 2 * x) h31 (by omega)
        simp [mul_add, ← mul_assoc, ← add_assoc] at hA3
        exact hA3
      have h33 : 4 + 10 * x + 8 * x ^ 2 ∈ A := by
        specialize hA3 (1 + 2 * x) h31 (3 + 4 * x) h32 (by omega)
        convert hA3 using 1
        ring
      exact h33
    -- Prove that 4 is in A. This uses the element 'a' (>2) and the previous lemma (h3). The generated number is divisible by 4. Since divisors are in A, 4 must be in A. It considers cases where 'a' is even or odd.
    have h4 : 4 ∈ A := by
      by_cases ha_even : Even a
      · specialize h3 a ha' ha
        apply hA2 (4 + 10 * a + 8 * a ^ 2) h3 4
        simp
        have ⟨k, hk⟩ := ha_even
        use (1 + 5 * k + 2 * a ^ 2)
        simp [hk]
        ring
      · simp at ha_even
        let m := 4 + 10 * a + 8 * a ^ 2
        have h_even' : Even m := by
          use 2 + 5 * a + 4 * a ^ 2
          ring
        specialize h3 m (by omega) (h3 a ha' ha)
        apply hA2 (4 + 10 * m + 8 * m ^ 2) h3 4
        simp
        have ⟨k, hk⟩ := h_even'
        use (1 + 5 * k + 2 * m ^ 2)
        simp [hk]
        ring
    -- Prove that 9 is in A, using (hA3) with 2 and 4, which are now known to be in A (1 + 2*4 = 9).
    have h5 : 9 ∈ A := by exact hA3 2 h2 4 h4 (by omega)
    -- Prove that 3 is in A, since it's a divisor of 9.
    have h6 : 3 ∈ A := by exact hA2 9 h5 3 (by norm_num)
    -- Prove that 5 is in A. First show 7 ∈ A (1+2*3), then 15 ∈ A (1+2*7), then 5 is a divisor of 15.
    have h7 : 5 ∈ A := by
      suffices 7 ∈ A by exact hA2 15 (hA3 2 h2 7 this (by omega)) 5 (by norm_num)
      exact hA3 2 h2 3 h6 (by omega)
    -- The core inductive step. Assume all integers up to n (for n≥5) are in A, then prove n+1 is also in A. It handles the cases for n+1 being odd or even separately to construct n+1 from smaller numbers known to be in A.
    have h8 : ∀ n ≥ 5, (∀ x ∈ Finset.Icc 1 n, x ∈ A) → (n + 1) ∈ A := by
      intro n hn hn1
      by_cases hno : Odd (n + 1)
      · obtain ⟨k, hk⟩ := hno
        specialize hA3 2 h2 k (hn1 k (by simp; omega)) (by omega)
        rwa [hk, add_comm]
      · simp at hno
        obtain ⟨k, hk⟩ := hno
        have hkn : 3 ≤ k ∧ k < n := by omega
        have hk1 : 2 * k - 1 ∈ A := by
          rw [two_mul, ← hk, Nat.add_sub_cancel]
          exact hn1 n (by simp; omega)
        have hk2 : 2 * k + 1 ∈ A := by
          specialize hA3 2 h2 k (hn1 k (by simp; omega)) (by omega)
          rwa [add_comm]
        specialize hA3 (2 * k - 1) hk1 (2 * k + 1) hk2 (by omega)
        specialize hA2 (1 + (2 * k - 1) * (2 * k + 1)) hA3 (2 * k)
        rw [hk, ← two_mul]
        apply hA2
        simp
        use 2 * k
        simp [mul_comm, ← Nat.sq_sub_sq, pow_two]
        rw [← Nat.add_sub_assoc, Nat.add_sub_cancel_left]
        nlinarith
    -- The final proof using set extensionality. We need to show that an element x is in A if and only if it's a positive integer.
    ext x
    refine ⟨fun h => ?_, fun h => ?_⟩
    -- The first direction (x ∈ A → x > 0) is given by the initial condition (hA).
    · simp
      exact hA x h
    -- The other direction (x > 0 → x ∈ A) is proven using strong induction. Base cases (1, 2, 3, 4) are proven individually. The inductive step for n ≥ 5 uses the lemma h8.
    · simp at h
      induction x using Nat.case_strong_induction_on
      · simp at h
      · rename_i n hn
        by_cases hn0 : n < 5
        · interval_cases n <;> simp [h1, h2, h4, h6, h7]
        · apply h8 n (by omega)
          exact fun x hx => hn x (by simp at hx; omega) (by simp at hx; omega)