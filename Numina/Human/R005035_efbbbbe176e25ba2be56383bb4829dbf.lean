import Mathlib
set_option maxHeartbeats 500000
/- Determine the number of pairs of integers $(m, n)$ such that

$$
\sqrt{n+\sqrt{2016}}+\sqrt{m-\sqrt{2016}} \in \mathbb{Q}
$$ -/
theorem algebra_605169 :
    {(m, n) : ℤ × ℤ | m - Real.sqrt 2016 ≥ 0 ∧ n + Real.sqrt 2016 ≥ 0 ∧ ∃ q : ℚ, Real.sqrt (n + Real.sqrt 2016) + Real.sqrt (m - Real.sqrt 2016) = q}.encard = 1 := by
  -- It suffices to show that (50, 50) is the only such pair.
  suffices {(m, n) : ℤ × ℤ | m - Real.sqrt 2016 ≥ 0 ∧ n + Real.sqrt 2016 ≥ 0 ∧ ∃ q : ℚ, Real.sqrt (n + Real.sqrt 2016) + Real.sqrt (m - Real.sqrt 2016) = q} = {(50, 50)} by
    rw [Set.encard_eq_one]
    use (50, 50)
  ext ⟨m, n⟩
  simp only [Set.mem_singleton_iff, Set.mem_setOf]
  -- Break the goal into two parts.
  apply Iff.intro
  . -- Show that (m, n) = (50, 50) is the only solution.
    rintro ⟨hm, hn, r, hr⟩
    have hr_def := hr
    -- Square both sides.
    replace hr : (Real.sqrt (n + Real.sqrt 2016) + Real.sqrt (m - Real.sqrt 2016)) ^ 2 = r ^ 2 := by rw [hr]
    rw [add_sq, Real.sq_sqrt hn, Real.sq_sqrt hm] at hr
    -- Rearrange the terms and square both sides.
    replace hr : 2 * Real.sqrt (n + Real.sqrt 2016) * Real.sqrt (m - Real.sqrt 2016) = r ^ 2 - m - n := by
      linarith only [hr]
    replace hr : (2 * Real.sqrt (n + Real.sqrt 2016) * Real.sqrt (m - Real.sqrt 2016)) ^ 2 = (r ^ 2 - m - n) ^ 2 := by
      rw [hr]
    -- Simplify to get (m - n)√2016 = (r² - m - n)²/4 - mn + 2016
    have hr' : (m - n) * Real.sqrt 2016 = (r ^ 2 - m - n) ^ 2 / 4 - m * n + 2016 := by
      rw [mul_assoc, mul_pow, mul_pow, Real.sq_sqrt hn, Real.sq_sqrt hm] at hr
      rw [<-hr, mul_comm (2 ^ 2 : ℝ), mul_div_assoc]
      norm_num
      ring_nf
      rw [Real.sq_sqrt (by norm_num)]
      ring_nf
    -- Show that √2016 is irrational.
    have h2016 : Irrational (Real.sqrt (2016 : ℤ)) := by
      rw [irrational_sqrt_intCast_iff_of_nonneg (by norm_num)]
      simp [IsSquare]
      intro s
      by_contra! hs
      -- Let t = |s| be the positive solution of t² = 2016.
      let t := |s|
      rw [<-pow_two, show s ^ 2 = t ^ 2 by rw [sq_abs]] at hs
      -- Now t is defined in such a way that 0 ≤ t.
      have ht : 0 ≤ t := by
        simp [t]
      linarith only [show 44 < t by nlinarith only [hs, ht], show t < 45 by nlinarith only [hs, ht]]
    -- Show that m = n, otherwise √2016 is rational.
    have hmn : m = n := by
      by_contra!
      symm at hr'
      rw [mul_comm _ (Real.sqrt 2016), <-div_eq_iff (by norm_cast; omega), show (2016 : ℝ) = (2016 : ℤ) by norm_num] at hr'
      rw [<-hr'] at h2016
      absurd h2016
      simp [Irrational]
      use ((r ^ 2 - m - n) ^ 2 / 4 - m * n + 2016) / (m - n)
      norm_cast
      rify
    -- Substitute m = n into hr.
    simp [hmn] at hr'
    -- Show that n² - 2016 = ((r² - 2n) / 2)².
    replace hr' : (n ^ 2 - 2016 : ℝ) = ((r ^ 2 - 2 * n) / 2) ^ 2 := by
      linarith only [hr']
    -- Show that 0 ≤ n² - 2016.
    have h₀ : 0 ≤ (n ^ 2 - 2016 : ℝ) := by
      linarith only [sq_nonneg ((r ^ 2 - 2 * n) / 2 : ℝ), hr']
    norm_cast at h₀
    have h₁ : 0 ≤ (n ^ 2 - 2016 : ℚ) := by
      norm_cast
    nth_rw 2 [<-sq_abs] at hr'
    -- Let x = |(r ^ 2 - 2 * n) / 2|.
    let x : ℚ := |(r ^ 2 - 2 * n) / 2|
    -- Show that x² = n² - 2016 for some x ∈ ℚ.
    have : x = |(r ^ 2 - 2 * n) / 2| := by
      simp only [x]
    norm_cast at hr' this
    rw [<-this] at hr'
    clear this
    rw [hmn] at hr_def hm ⊢
    -- Show that x is a natural number. In other words, there exists p ∈ ℕ such that p = x.
    have h₀ := irrational_sqrt_intCast_iff_of_nonneg h₀
    have h₁ := irrational_sqrt_ratCast_iff_of_nonneg h₁
    -- Since n² - 2016 is a square of rational number but itself an integer, it is a square of integer.
    simp at h₀ h₁
    have h₂ := Iff.trans h₀.symm h₁
    clear h₀ h₁
    simp at h₂
    apply Iff.not at h₂
    simp [IsSquare] at h₂
    have hp : ∃ x : ℚ, n ^ 2 - 2016 = x * x := by
      use x
      rw [<-pow_two]
      norm_cast at hr' ⊢
    rw [<-h₂] at hp
    obtain ⟨s, hp⟩ := hp
    -- Let p = |s|.
    let p := s.natAbs
    rw [<-pow_two, show s ^ 2 = p ^ 2 by simp [p]] at hp
    -- Show that r² ≥ 2n.
    have hrn : (Real.sqrt (n + Real.sqrt 2016) + Real.sqrt (n - Real.sqrt 2016)) ^ 2 ≥ 2 * n := by
      rw [add_sq, Real.sq_sqrt hn, Real.sq_sqrt hm]
      linarith only [show 0 ≤ Real.sqrt (n + Real.sqrt 2016) * Real.sqrt (n - Real.sqrt 2016) by positivity]
    rw [hr_def] at hrn
    -- Show that r² = 2n + 2p.
    rify at hp
    rw [mul_assoc, <-Real.sqrt_mul hn, hmn, <-sq_sub_sq, Real.sq_sqrt (by norm_num), hp, mul_pow, Real.sq_sqrt (by positivity), <-mul_pow] at hr
    rw [sq_eq_sq₀ (by positivity) (by linarith only [hrn])] at hr
    clear_value p
    clear hr' h₀ h₁ h₂ s x
    norm_cast at hr
    -- Show that n ≥ 0.
    replace hn : n ≥ 0 := by
      rify
      linarith only [hm, show 0 ≤ Real.sqrt 2016 by positivity]
    -- Show that (n-p)(n+p) = 2016.
    replace hp : (n - p) * (n + p) = 2016 := by
      qify
      ring_nf at hp ⊢
      apply sub_eq_of_eq_add
      rw [add_comm, <-sub_eq_add_neg] at hp
      symm at hp ⊢
      apply add_eq_of_eq_sub at hp
      rw [add_comm] at hp
      norm_cast at hp ⊢
    -- Show that r²=2(n+p).
    replace hr : r ^ 2 = 2 * (n + p) := by
      push_cast at hr
      linarith only [hr]
    -- Show that r is a integer. In other words, there exists q ∈ ℕ such that q = |r|.
    have h₀ := irrational_sqrt_intCast_iff_of_nonneg (show 0 ≤ 2 * (n + p) by positivity)
    have h₁ := irrational_sqrt_ratCast_iff_of_nonneg (show 0 ≤ (2 * (n + p) : ℚ) by positivity)
    simp at h₀ h₁
    have h₂ := Iff.trans h₀.symm h₁
    clear h₀ h₁
    simp at h₂
    apply Iff.not at h₂
    simp [IsSquare] at h₂
    have hq : ∃ x : ℚ, 2 * (n + p) = x * x := by
      use r
      rw [<-pow_two]
      norm_cast at hr ⊢
      exact hr.symm
    rw [<-h₂] at hq
    obtain ⟨s, hq⟩ := hq
    -- Let q = |s|.
    let q := s.natAbs
    rw [<-pow_two, show s ^ 2 = q ^ 2 by simp [q]] at hq
    clear_value q
    clear h₂ hr hr_def hrn s r
    -- Show that n - p ≥ 0.
    have hnp : n - p ≥ 0 := by
      nlinarith only [show 0 ≤ n + p by positivity, hp]
    -- Show that n + p is even.
    have hnp' : Even (n + p) := by
      -- It is a classical result that 2 ∣ q² implies 2 ∣ q and hence 2 ∣ n + p.
      have : 2 ∣ (q ^ 2 : ℤ) := by
        rw [<-hq]
        apply dvd_mul_right
      norm_cast at this
      -- Since 2 ∣ q², so 2 ∣ q.
      replace this : 2 ∣ q := by
        apply Nat.Prime.dvd_of_dvd_pow (Nat.prime_two) this
      -- Since 2 ∣ q, so 2 * 2 ∣ q² = 2 * (n+p).
      replace this : 2 * 2 ∣ 2 * (n + p) := by
        calc
          (2 * 2 : ℤ) = 2 ^ 2 := by norm_num
          _ ∣ (q ^ 2 : ℤ) := by
            norm_cast
            apply pow_dvd_pow_of_dvd this
          _ = 2 * (n + p) := by rw [<-hq]
      rw [mul_dvd_mul_iff_left (by norm_num)] at this
      rw [even_iff_two_dvd]
      exact this
    -- Show that n - p is even.
    have hnp'' : Even (n - p) := by
      -- It is easy since n + p is even.
      rw [show n - p = (n + p) + 2 * -p by ring]
      apply Even.add
      . exact hnp'
      . rw [even_iff_two_dvd]
        apply dvd_mul_right
    rw [even_iff_two_dvd, dvd_iff_exists_eq_mul_right] at hnp''
    obtain ⟨k, hnp''⟩ := hnp''
    rw [hnp'', mul_assoc, mul_comm, mul_assoc, mul_comm _ 2] at hp
    -- Show k ≥ 0.
    have hk : k ≥ 0 := by
      nlinarith only [hnp, hnp'']
    rw [hq] at hp
    -- Consider possible factorizations of 2016.
    let x := (k.natAbs, q ^ 2)
    have hfactor : x.1 * x.2 = 2016 ∧ 2016 ≠ 0 := by
      simp only [x]
      zify
      rw [abs_of_nonneg hk]
      exact ⟨hp, by norm_num⟩
    rw [<-Nat.mem_divisorsAntidiagonal] at hfactor
    -- Use the computer to find the factors of 2016 (native_decide is necessary).
    rw [show Nat.divisorsAntidiagonal 2016 = {(1, 2016), (2, 1008), (3, 672), (4, 504), (6, 336), (7, 288), (8, 252), (9, 224), (12, 168), (14, 144), (16, 126), (18, 112), (21, 96), (24, 84), (28, 72), (32, 63), (36, 56), (42, 48), (48, 42), (56, 36), (63, 32), (72, 28), (84, 24), (96, 21), (112, 18), (126, 16), (144, 14), (168, 12), (224, 9), (252, 8), (288, 7), (336, 6), (504, 4), (672, 3), (1008, 2), (2016, 1)} by native_decide] at hfactor
    simp [x] at hfactor
    rcases hfactor with (⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩ | ⟨h₀, h₁⟩)
    -- Use native_decide to cancel all cases where q ^ 2 is not a square.
    all_goals
      have h₂ : IsSquare (q ^ 2) := by
        simp [IsSquare]
        use q
        rw [pow_two]
      rw [h₁] at h₂
      try
        absurd h₂
        native_decide
    . -- When q² = 144, we get the solution (m, n) = (50, 50).
      zify at h₀
      rw [abs_of_nonneg hk] at h₀
      rw [show 144 = 12 ^ 2 by norm_num] at h₁
      apply Nat.pow_left_injective (by norm_num) at h₁
      simp [h₀] at hnp''
      simp [h₁] at hq
      simp
      omega
    . -- When q² = 36, a contradiction.
      zify at h₀
      rw [abs_of_nonneg hk] at h₀
      rw [show 36 = 6 ^ 2 by norm_num] at h₁
      apply Nat.pow_left_injective (by norm_num) at h₁
      simp [h₀] at hnp''
      simp [h₁] at hq
      omega
    . -- When q² = 16, a contradiction.
      zify at h₀
      rw [abs_of_nonneg hk] at h₀
      rw [show 16 = 4 ^ 2 by norm_num] at h₁
      apply Nat.pow_left_injective (by norm_num) at h₁
      simp [h₀] at hnp''
      simp [h₁] at hq
      omega
    . -- When q² = 9, a contradiction.
      zify at h₀
      rw [abs_of_nonneg hk] at h₀
      rw [show 9 = 3 ^ 2 by norm_num] at h₁
      apply Nat.pow_left_injective (by norm_num) at h₁
      simp [h₀] at hnp''
      simp [h₁] at hq
      omega
    . -- When q² = 4, a contradiction.
      zify at h₀
      rw [abs_of_nonneg hk] at h₀
      rw [show 4 = 2 ^ 2 by norm_num] at h₁
      apply Nat.pow_left_injective (by norm_num) at h₁
      simp [h₀] at hnp''
      simp [h₁] at hq
      omega
    . -- When q² = 1, a contradiction.
      zify at h₀
      rw [abs_of_nonneg hk] at h₀
      rw [show 1 = 1 ^ 2 by norm_num] at h₁
      apply Nat.pow_left_injective (by norm_num) at h₁
      simp [h₀] at hnp''
      simp [h₁] at hq
      omega
  . -- Show that (m, n) = (50, 50) is indeed a solution.
    rintro ⟨hm, hn⟩
    simp [show 0 ≤ 50 + Real.sqrt 2016 by positivity]
    rw [Real.sqrt_le_iff]
    norm_num
    -- √(50 + √2016) + √(50 - √2016) = 12. The remaining is just boring calculations.
    use 12
    rw [<-sq_eq_sq₀ (by positivity) (by positivity), add_sq, Real.sq_sqrt (by positivity), Real.sq_sqrt (by simp; rw [Real.sqrt_le_iff]; norm_num)]
    suffices Real.sqrt (50 + Real.sqrt 2016) * Real.sqrt (50 - Real.sqrt 2016) = 22 by
      rw [mul_assoc, this]
      norm_num
      linarith
    rw [<-Real.sqrt_mul (by positivity), <-sq_eq_sq₀ (by positivity) (by positivity), Real.sq_sqrt]
    all_goals
      rw [<-sq_sub_sq, Real.sq_sqrt (by positivity)]
      norm_num
