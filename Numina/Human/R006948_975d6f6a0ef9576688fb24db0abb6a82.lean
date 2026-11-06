import Mathlib
/- Compute the sum of all positive integers $n$ for which the expression

$$
\frac{n+7}{\sqrt{n-1}}
$$

is an integer. -/
theorem number_theory_610259 (A : Finset ℕ) (hA : A = {n : ℕ | n > 1 ∧ (∃ k : ℕ, (n + (7 : ℝ)) / √(n - 1) = k)}) : ∑ a ∈ A, a = 89:= by
  -- First we prove that the set of valid n values is exactly {2, 5, 17, 65}
  have h1 : {n : ℕ | n > 1 ∧ (∃ k : ℕ, (n + (7 : ℝ)) / √(n - 1) = k)} = {2, 5, 17, 65}:= by
    -- We prove this by showing both inclusions
    ext n
    constructor
    -- Forward direction: if n satisfies the condition, then n is in {2, 5, 17, 65}
    .
      intro h
      simp at h
      rcases h with ⟨h1, h2⟩
      rcases h2 with ⟨k, hk⟩
      have h:= h1
      rify at h1
      -- Since n > 1, we have n-1 > 0, which ensures √(n-1) is well-defined
      replace h1 : (↑n : ℝ) - 1 > 0:= by linarith
      field_simp at hk
      -- The integer k must be non-zero
      have hk1 : k ≠ 0:= by
        by_contra H
        subst k
        simp at hk
        linarith
      -- This lemma shows that if √a is rational, then it must be an integer
      have h2 : ∀ a : ℕ, (∃ r : ℚ, √a = r) → ∃ t : ℕ, √a = t:= by
        intro a h
        rcases h with ⟨r, hr⟩
        have h2:= Rat.mul_self_den r
        have h:= hr
        replace hr : √a ^ 2 = r ^ 2:= by rw [hr]
        field_simp at hr
        replace hr : a = r ^ 2:= by rify ; linarith
        have g2 : (↑a : ℚ).den = 1:= by exact rfl
        rw [show r * r = r ^ 2 by ring_nf] at h2
        rw [hr, h2] at g2
        simp at g2
        rw [show r = r.num / r.den by exact Eq.symm (Rat.num_div_den r)] at h
        rw [g2] at h
        simp at h
        use (r.num).natAbs
        rw [show (↑(r.num).natAbs : ℝ) = (↑(r.num).natAbs : ℤ) by exact rfl]
        simp
        rw [h]
        rw [abs_of_nonneg (by rw [←h] ; positivity)]
      -- Apply the lemma to n-1
      specialize h2 (n - 1) (⟨(n + 7) / k, by field_simp ; linarith⟩)
      rcases h2 with ⟨t, ht⟩
      -- t divides n-1
      have ht1 : t ∣ n - 1:= by
        field_simp at ht
        replace ht : √(n - 1) ^ 2 = t ^ 2:= by rw [ht]
        field_simp at ht
        replace ht : n - 1 = t ^ 2:= by
          rify
          field_simp
          exact ht
        rw [ht]
        exact Dvd.intro_left (t.pow 1) rfl
      -- n+7 = k*t
      replace hk : n + 7 = k * t:= by
        rify
        rw [←ht]
        field_simp
        exact hk
      -- t divides n+7
      replace hk : t ∣ n + 7:= by rw [hk] ; simp
      -- Rewrite n+7 as (n-1)+8
      rw [show n + 7 = n - 1 + 2 ^ 3 by omega] at hk
      replace hk : t ∣ 2 ^ 3:= by exact (Nat.dvd_add_iff_right ht1).mpr hk
      have g1 : Nat.Prime 2:= by norm_num
      -- Since t divides 2^3, t must be a power of 2 with exponent ≤ 3
      replace hk : ∃ s : ℕ, s ≤ 3 ∧ t = 2 ^ s:= by exact (Nat.dvd_prime_pow g1).mp hk
      rcases hk with ⟨s, hs1, hs2⟩
      -- n = t² + 1
      replace ht : n = t ^ 2 + 1:= by
        replace ht : √(n - 1) ^ 2 = t ^ 2:= by
          field_simp at ht
          rw [ht]
        field_simp at ht
        rify
        linarith
      -- s must be 0, 1, 2, or 3
      replace hs1 : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3:= by omega
      -- Check each case to find the possible values of n
      rcases hs1 with hs1 | hs1 | hs1 | hs1
      all_goals
        subst s
        simp at hs2
        subst t
        simp at ht
        subst n
        simp
    -- Reverse direction: if n is in {2, 5, 17, 65}, then it satisfies the condition
    .
      intro h
      simp at h
      rcases h with h | h | h | h
      -- Case n = 2
      .
        subst n
        simp
        norm_num
        use 9
        simp
      -- Case n = 5
      .
        subst n
        simp
        norm_num
        rw [show (4 : ℝ) = 2 ^ 2 by linarith]
        field_simp
        use 6
        simp
        linarith
      -- Case n = 17
      .
        subst n
        simp
        norm_num
        rw [show (16 : ℝ) = 4 ^ 2 by linarith]
        field_simp
        use 6
        simp
        linarith
      -- Case n = 65
      .
        subst n
        simp
        norm_num
        rw [show (64 : ℝ) = 8 ^ 2 by linarith]
        field_simp
        use 9
        simp
        linarith
  -- Use the characterization of A to compute the sum
  rw [h1] at hA
  have h2 : A = (↑A : Set ℕ).toFinset:= by simp
  simp [hA] at h2
  rw [h2]
  simp
