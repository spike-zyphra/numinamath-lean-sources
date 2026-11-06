import Mathlib

open Real Set

/- Let $A$ be an acute angle such that $\tan A = 2 \cos A.$ Find the number of positive integers $n$ less than or equal to $1000$ such that $\sec^n A + \tan^n A$ is a positive integer whose units digit is $9.$ -/
theorem algebra_98656 (A : Real) (hA : A ∈ Ioo 0 (π / 2)) (h : tan A = 2 * cos A) :
    {n : ℕ | 0 < n ∧ n ≤ 1000 ∧ ∃ k : ℕ, (1 / cos A)^n + (tan A)^n = 10 * k + 9}.ncard = 167 := by
  -- A ∈ (0, π / 2) so 0 < cos A
  have hcos0 : 0 < cos A := by
    apply Real.cos_pos_of_mem_Ioo
    apply Set.mem_of_subset_of_mem _ hA
    apply Ioo_subset_Ioo_left
    linarith [Real.pi_pos]
  -- Prove an auxiliary inequality: 0 < √17 - 1
  have ineq : 0 < √17 - 1 := by
    suffices 1 < √17 by linarith
    rw [← Real.sqrt_one]
    apply Real.sqrt_lt_sqrt zero_le_one (by norm_num)
  -- Solve the equation tan A = 2 * cos A and obtain cos A ^ 2 = (√17 - 1) / 8
  have hcos2 : cos A ^ 2 = (√17 - 1) / 8 := by
    -- Rewrite the equation as sin A = 2 * cos A ^ 2
    field_simp [Real.tan_eq_sin_div_cos] at h
    -- Rewrite the equation again as 2 * sin A ^ 2 + sin A - 2 = 0 (replace cos A ^ 2 with 1 - sin A ^ 2)
    replace h : 2 * (sin A * sin A) + 1 * sin A + (-2) = 0 := by
      rw [mul_assoc, ← pow_two, Real.cos_sq'] at h
      linear_combination h
    -- The discriminant of this quadratic equation is √17 ^ 2
    have hd : discrim (2 : ℝ) 1 (-2) = √17 * √17 := by simp [discrim]; norm_num
    rw [quadratic_eq_zero_iff (by norm_num) hd] at h
    -- The quadratic equation has two roots:
    -- sin A = (-1 + √17) / 4 and sin A = (-1 - √17) / 4
    cases' h with h h
    -- If sin A = (-1 + √17) / 4 then we get cos A ^ 2 = 1 - sin A ^ 2 = (√17 - 1) / 8
    · rw [Real.cos_sq', h]
      ring_nf
      simp only [one_div, Nat.ofNat_nonneg, sq_sqrt]
      ring
    -- If sin A = (-1 - √17) / 4 then we obtain a contradiction using the fact that 0 < sin A
    · have h0 : 0 < sin A := by
        apply Real.sin_pos_of_mem_Ioo
        apply Set.mem_of_subset_of_mem _ hA
        apply Ioo_subset_Ioo_right
        linarith [Real.pi_pos]
      contrapose! h0
      rw [h]
      linarith
  -- We get cos A = √((√17 - 1) / 8)
  have hcos : cos A = √((√17 - 1) / 8) := by
    symm
    rw [Real.sqrt_eq_iff_eq_sq (by linarith) (le_of_lt hcos0), hcos2]
  -- Let a = √((√17 - 1) / 2)
  set a := √((√17 - 1) / 2)
  -- Let b = √((√17 + 1) / 2)
  set b := √((√17 + 1) / 2)
  have h2 : √4 = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, sqrt_sq zero_le_two]
  -- It is easy to show that a * b = 2
  have hab : a * b = 2 := by
    dsimp [a, b]
    rw [←Real.sqrt_mul (by linarith)]
    ring_nf
    norm_num [h2]
  -- We have tan A = 2 * cos A = 2 * √((√17 - 1) / 8) = a
  have htan : tan A = a := by
    simp_rw [a, h, hcos]
    nth_rw 1 [← h2, ← sqrt_mul (by norm_num)]
    ring_nf
  -- We have 1 / cos A = 1 / √((√17 - 1) / 8) = b
  have hsec : 1 / cos A = b := by
    simp_rw [b, hcos]
    field_simp
    rw [← sqrt_mul (by norm_num), ← sqrt_mul (by positivity)]
    ring_nf
    rw [sq_sqrt (by norm_num), show -1 + 17 = (16 : ℝ) by norm_num]
  -- Let s(n) = a^n + b^n
  set s : ℕ → ℝ := fun n => a ^ n + b ^ n
  -- Prove the following recursive formula for s:
  -- s(n) = s(n - k) * s(k) - 2^k * s(n - 2 * k) for all 2 * k ≤ n
  have hsk {n k : ℕ} (hk : 2 * k ≤ n) : s n = s (n - k) * s k - 2 ^ k * s (n - 2 * k) := by
    -- The result follows from the definition of s(n):
    -- s(n) = a^n + b^n
    --      = (a^(n - k) + b^(n - k)) * (a^k + b^k) - (a^(n - k) * b^k + b^(n - k) * a^k)
    --      = s(n - k) * s(k) - (a * b)^k * (a^(n - 2 * k) + b^(n - 2 * k))
    --      = s(n - k) * s(k) - 2^k * s(n - 2 * k) (because a * b = 2).
    nth_rw 1 [← hab]
    ring_nf
    simp_rw [←pow_add, show n - k + k = n by omega, mul_assoc, ← pow_add]
    rw [show k + (n - k * 2) = n - k by omega]
    ring
  -- We also have s(n)^2 = (a^n + b^n)^2 = (a^(2 * n) + b^(2 * n)) + 2 * (a * b)^n = s(2 * n) + 2^(n + 1).
  have hs2 n : s n ^ 2 = s (2 * n) + 2 ^ (n + 1) := by
    ring_nf
    rw [← mul_pow, hab]
    ring
  -- Compute s(0) = 2
  have s0 : s 0 = 2 := by simp [s]; norm_num
  -- Compute s(2) = √17
  have s2 : s 2 = √17 := by
    dsimp [s, a, b]
    rw [sq_sqrt (by positivity), sq_sqrt (by positivity)]
    ring
  -- Compute s(4) = s(2)^2 - 2^(2 + 1) = 17 - 8 = 9
  have s4 : s 4 = 9 := by
    have := hs2 2
    rw [s2, sq_sqrt (by norm_num)] at this
    norm_num at this
    linarith
  -- Prove that s(4 * n) is an integer
  have hs_int n : ∃ k : ℤ, s (4 * n) = k := by
    -- A proof by strong induction.
    induction' n using Nat.strongRec with n ih
    -- Consider 3 cases: n = 0, n = 1, or 2 ≤ n
    rcases show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega with hn | hn | hn
    -- If n = 0 then s(0) = 2 ∈ ℤ
    · use 2; simp [hn, s0]
    -- If n = 1 then s(4) = 9 ∈ ℤ
    · use 9; simp [hn, s4]
    -- Now consider the case 2 ≤ n.
    -- Set k = 4 in the recursive formula for s (hsk) and get
    -- s (4 * n) = s(4 * n - 4) * 9 - 16 * s(4 * n - 8)
    have eq := s4 ▸ hsk (show 2 * 4 ≤ 4 * n by omega)
    rw [eq]
    -- Both s(4 * n - 4) = s(4 * (n - 1)) and s(4 * n - 8) = s(4 * (n - 2)) are integers
    -- (by the induction hypothesis).
    have ⟨k1, hk1⟩ := ih (n - 1) (by omega)
    have ⟨k2, hk2⟩ := ih (n - 2) (by omega)
    -- We conclude that s(4 * n) is also an integer.
    use k1 * 9 - 2 ^ 4 * k2
    rw [show 4 * n - 4 = 4 * (n - 1) by omega, show 4 * n - 2 * 4 = 4 * (n - 2) by omega] at eq ⊢
    rw [hk1, hk2] at eq ⊢
    push_cast
    ring
  -- Construct an integer sequence r(n) with the following properties:
  -- s(4 * n) = r(n) for all n,
  -- r(0) = 2, r(1) = 9 and r(n + 2) = 9 * r(n + 1) - 16 * r(n) for all n.
  have ⟨r, hrs, hr0, hr1, hr⟩ : ∃ r : ℕ → ℤ, (∀ n, s (4 * n) = r n) ∧ r 0 = 2 ∧ r 1 = 9 ∧ (∀ n, r (n + 2) = 9 * r (n + 1) - 16 * r n) := by
    -- It is enough to take r(n) = s(4 * n) (it is an integer by the previous result).
    set r := fun n => Classical.choose (hs_int n)
    have hr : ∀ n, r n = s (4 * n) := by
      have := fun n => @Classical.choose_spec _ _ (hs_int n)
      intro n
      simp only [← this, r]
    use r
    rify
    simp [hr, s0, s4]
    intro n
    rw [hsk (show 2 * 4 ≤ 4 * (n + 2) by omega), s4]
    rw [show 4 * (n + 2) - 4 = 4 * (n + 1) by omega, show 4 * (n + 2) - 2 * 4 = 4 * n by omega]
    ring
  -- Show that s(4 * n + 2) is irrational for all n.
  have hs_irr2 n : Irrational (s (2 * (2 * n + 1))) := by
    clear * - hs_int s2 hsk
    -- It is enough to show that s(4 * n + 2) = k √17 for some integer k.
    suffices eq : ∃ (k : ℤ), s (2 * (2 * n + 1)) = k * √17 by
      have ⟨k, hk⟩ := eq
      rw [hk]
      -- Observer that k ≠ 0 because s(n) > 0 for all n
      have hk0 : k ≠ 0 := by
        contrapose! hk
        simp [hk]
        apply ne_of_gt
        positivity
      -- k √17 is irrational if √17 is irrational.
      apply Irrational.int_mul _ hk0
      rw [show (17 : ℝ) = (17 : ℕ) by simp]
      -- √17 is irrational as a square root of a prime number.
      apply Nat.Prime.irrational_sqrt
      norm_num
    rw [show 2 * (2 * n + 1) = 4 * n + 2 by linarith]
    -- Show that s(4 * n + 2) = k √17 for some k (by induction).
    induction n with
    -- If n = 0 then s(2) = 1 * √17.
    | zero => use 1; simp [s2]
    | succ n ih =>
      -- Consider s(4 * (n + 1) + 2).
      -- We have s(4 * (n + 1)) = k1 for some integer k1.
      have ⟨k1, hk1⟩ := hs_int (n + 1)
      -- We also have s(4 * n + 2)) = k2 √17 for some integer k2 from the induction hypothesis.
      have ⟨k2, hk2⟩ := ih
      -- Take k1 - 4 * k2 and show that s(4 * (n + 1) + 2) = (k1 - 4 * k2)√17
      use k1 - 4 * k2
      -- The result follows from the recursive formula for s (hsk) with k = 2.
      simp [hsk (show 2 * 2 ≤ 4 * (n + 1) + 2 by linarith)]
      rw [hk1, s2, show 4 * (n + 1) - 2 = 4 * n + 2 by omega, hk2]
      ring
  -- Show that s(2 * n + 1) is irrational.
  have hs_irr1 n : Irrational (s (2 * n + 1)) := by
    -- s(2 * n + 1) is irrational if s(2 * n + 1)^2 is irrational
    apply Irrational.of_mul_self
    -- s(2 * n + 1)^2 = s(4 * n + 2) + 2^(2 * n + 2) (by hs2)
    rw [← pow_two, hs2, show (2 : ℝ) ^ (2 * n + 1 + 1) = (2 ^ (2 * n + 1 + 1) : ℕ) by simp]
    -- s(4 * n + 2) is irrational and 2^(2 * n + 2) is integer, so s(2 * n + 1)^2 is irrational.
    apply Irrational.add_nat
    exact hs_irr2 n
  -- Prove that r(3 * n) % 10 ≠ 9 (it equals to 2 when n = 0 and to 7 when n > 0)
  -- and r(3 * n + 1) % 10 = r(3 * n + 2) % 10 = 9.
  have r10 n : r (3 * n) % 10 = (if n = 0 then 2 else 7) ∧ r (3 * n + 1) % 10 = 9 ∧ r (3 * n + 2) % 10 = 9 := by
    -- Proof by induction.
    induction n with
    -- For n = 0 we have r(0) = 2, r(1) = 9, r(2) = 9 * r(1) - 16 * r(0) = 81 - 32 = 49.
    | zero => simp [hr0, hr1, hr]
    | succ n ih =>
      -- Consider r(3 * (n + 1) + x)
      simp [hr]
      -- Show that r(3 * (n + 1)) % 10 = 7.
      have h1 : r (3 * (n + 1)) % 10 = 7 := by
        -- We have
        -- r(3 * (n + 1)) = r(3 * n + 1 + 2) = 9 * r(3 * n + 2) - 16 * r(3 * n + 1).
        -- r(3 * n + 2) % 10 = 9 and r(3 * n + 1) % 10 = 9 (by the induction hypothesis), so
        -- r(3 * (n + 1)) % 10 = (9 * 9 - 16 * 9) % 10 = 7.
        rw [show 3 * (n + 1) = 3 * n + 3 by omega, hr, Int.sub_emod]
        rw [Int.mul_emod, ih.2.2]
        norm_num
        rw [Int.mul_emod, ih.2.1]
        norm_num
      -- Show that r(3 * (n + 1) + 1) % 10 = 9.
      have h2 : r (3 * (n + 1) + 1) % 10 = 9 := by
        -- We have
        -- r(3 * (n + 1) + 1) = r(3 * n + 2 + 2) = 9 * r(3 * n + 3) - 16 * r(3 * n + 2).
        -- We showed that r(3 * n + 3) % 10 = 7 and we know that r(3 * n + 2) % 10 = 9, so
        -- r(3 * (n + 1) + 1) % 10 = (9 * 7 - 16 * 9) % 10 = 9.
        rw [show 3 * (n + 1) + 1 = 3 * n + 4 by omega, hr, Int.sub_emod]
        rw [Int.mul_emod, show 3 * n + 2 + 1 = 3 * (n + 1) by omega, h1]
        norm_num
        rw [Int.mul_emod, ih.2.2]
        norm_num
      -- The final result r(3 * (n + 1) + 2) % 10 = 9 follows from
      -- r(3 * (n + 1) + 2) = 9 * r(3 * (n + 1) + 1) - 16 * r(3 * (n + 1)).
      simp only [h1, h2, Int.sub_emod, Int.mul_emod, Int.reduceMod, dvd_refl, Int.emod_emod_of_dvd,
        Int.reduceMul, true_and]
      norm_num
  -- Now start to prove the main goal.
  -- It is enough to show that the set from the theorem statement is equal to
  -- 4 * ((0, 250] \ {n | n ∈ (0, 250] ∧ 3 ∣ n})
  -- (all positive integers in (0, 250] which are not divisible by 3, multiplied by 4).
  suffices eq : {n : ℕ | 0 < n ∧ n ≤ 1000 ∧ ∃ k : ℕ, (1 / cos A)^n + (tan A)^n = 10 * k + 9}
      = (4 * ·) '' (Finset.Ioc 0 250 \ (Finset.filter (fun n => 3 ∣ n) (Finset.Ioc 0 250))) by
    have hinj : (4 * ·).Injective := by intro x y; simp
    rw [eq, Set.ncard_image_of_injective _ hinj, Set.ncard_diff (by apply Finset.filter_subset)]
    -- The cardinality of (0, 250] is 250.
    simp_rw [ncard_coe_Finset, Nat.card_Ioc]
    -- Compute the cardinality of {n | n ∈ (0, 250] ∧ 3 ∣ n}.
    have : (Finset.filter (fun n => 3 ∣ n) (Finset.Ioc 0 250)).card = ({n ∈ Finset.Ioc 0 250 | n ≡ 0 [MOD 3]}).card := by
      congr; ext n
      rw [Nat.modEq_zero_iff_dvd]
    zify at this
    -- The cardinality of {n | n ∈ (0, 250] ∧ 3 ∣ n} is 83.
    rw [Nat.Ioc_filter_modEq_card _ _ (by norm_num)] at this
    norm_num at this
    -- We get 250 - 83 = 167.
    norm_cast at this
  ext n
  simp only [inv_pow, mem_setOf_eq, Finset.coe_Ioc, Finset.coe_filter, Finset.mem_Ioc,
    mem_image, mem_diff, mem_Ioc, not_and, and_imp, hsec, htan]
  rw [show b ^ n + a ^ n = s n by ring]
  constructor
  -- Show that n ∈ (0, 1000] and s(n) = 10 * k + 9 implies that
  -- n = 4 * x for some x and 3 does not divide x.
  · intro ⟨hn1, hn2, k, hk⟩
    -- Consider two cases: 4 divides n and 4 does not divide n
    by_cases hn4 : 4 ∣ n
    · have ⟨m, hmn⟩ := hn4
      -- If 4 divides n then n = 4 * m for some m. Let x = m.
      use m
      simp [show 0 < m ∧ m ≤ 250 by omega, hmn]
      -- Show that ¬ (3 ∣ m). Assume that 3 ∣ m and show that s(n) % 10 ≠ 9.
      contrapose! r10
      have ⟨t, ht⟩ := r10
      subst m n
      rw [hrs] at hk
      norm_cast at hk
      use t
      rw [hk]
      simp [Int.add_emod]
      split_ifs <;> norm_num
    -- Suppose that 4 does not divide n and show that s(n) is irrational.
    suffices Irrational (s n) by
      apply_fun Irrational at hk
      rw [show 10 * (k : ℝ) + 9 = (10 * k + 9 : ℕ) by simp] at hk
      simp only [Nat.not_irrational, this] at hk
      contradiction
    -- Either n % 2 = 1 or n % 4 = 2.
    cases' show n % 2 = 1 ∨ n % 4 = 2 by omega with hn hn
    · have := Nat.mod_add_div n 2
      -- If n % 2 = 1 then n = 2 * (n / 2) + 1.
      rw [← this, hn, add_comm]
      -- We proved that s(2 * (n / 2) + 1) is irrational.
      exact hs_irr1 _
    · have := Nat.mod_add_div n 4
      -- If n % 4 = 2 then n = 4 * (n / 4) + 2.
      rw [← this, hn, add_comm, show 4 * (n / 4) + 2 = 2 * (2 * (n / 4) + 1) by omega]
      -- We proved that s(4 * (n / 2) + 2) is irrational.
      exact hs_irr2 _
  -- Show that k ∈ (0, 250] and ¬ (3 ∣ k) implies that s(4 * k) is an integer such that
  -- s(4 * k) % 10 = 9.
  · intro ⟨k, ⟨hk, hk3⟩, hkn⟩
    specialize hk3 hk.1 hk.2
    refine ⟨by omega, by omega, ?_⟩
    rw [← hkn, hrs]
    -- We have s(n) = s(4 * k) = r(k) and r(k) % 10 = 9 (because k = 3 * m + 1 or k = 3 * m + 2).
    have hr : r k % 10 = 9 := by
      have hk_eq := add_comm (k % 3) _ ▸ (Nat.mod_add_div k 3).symm
      cases' show k % 3 = 1 ∨ k % 3 = 2 by omega with hk hk <;> rw [hk] at hk_eq
      · rw [hk_eq, (r10 (k / 3)).2.1]
      · rw [hk_eq, (r10 (k / 3)).2.2]
    -- r(k) = s(4 * k) is positive so r(k) = m for some natural number m.
    have ⟨m, hm⟩ : ∃ m : ℕ, r k = m := by
      use (r k).natAbs
      rw [Int.natAbs_of_nonneg]
      rify
      rw [← hrs]
      positivity
    -- r(k) % 10 = 9 implies that m % 10 = 9.
    replace hr : m % 10 = 9 := by zify; simp [← hm, hr]
    -- We have r(k) = m = 10 * (m / 10) + 9.
    have hm1 := add_comm (m % 10) _ ▸ (Nat.mod_add_div m 10).symm
    use m / 10
    norm_cast
    nth_rw 1 [hm, hm1, hr]
    rfl