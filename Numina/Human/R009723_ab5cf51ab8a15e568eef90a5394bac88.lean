import Mathlib

/- Find all the pairs $(m, n)$ of integers which satisfy the equation

$$
m^{5}-n^{5}=16 m n
$$-/
theorem algebra_605496 :
    {(m, n) : ℤ × ℤ | m ^ 5 - n ^ 5 = 16 * m * n} = {(0, 0), (-2, 2)} := by
  -- Break the goal into two parts.
  ext ⟨m, n⟩
  apply Iff.intro
  . -- Show that (m, n) = (0, 0) or (-2, 2) are the only solutions.
    intro h₀
    -- Consider the cases mn = 0 and mn ≠ 0.
    by_cases h₁ : m * n = 0
    . simp at h₁
      rcases h₁ with (h₁ | h₁)
      <;> simp_all
    . -- Now assume that m * n ≠ 0.
      simp [<-ne_eq] at h₁
      -- Let d = gcd(m, n).
      let d := m.gcd n
      -- Let a = m / d and b = n / d.
      let a := m / d
      let b := n / d
      -- Show that a and b are coprime.
      have h₂ : a.gcd b = 1 := by
        simp [a, b]
        apply Int.gcd_div_gcd_div_gcd
        rw [Int.gcd_pos_iff]
        tauto
      have hx : m = d * a := by
        simp [a]
        rw [Int.mul_ediv_cancel']
        exact Int.gcd_dvd_left
      have hy : n = d * b := by
        simp [b]
        rw [Int.mul_ediv_cancel']
        exact Int.gcd_dvd_right
      -- Substitute m and n by d * a and d * b and simplify the equation to get d³a⁵-d³b⁵=16ab.
      simp [hx, hy] at h₀
      rw [mul_pow, mul_pow] at h₀
      ring_nf at h₀
      rw [<-mul_sub, show (d : ℤ) ^ 5 = d ^ 2 * d ^ 3 by ring_nf] at h₀
      rw [mul_assoc, mul_assoc, mul_assoc, Int.mul_eq_mul_left_iff (by by_contra!; simp at this; rw [this] at hx; omega)] at h₀
      -- Show that a ∣ d³b⁵ and hence a ∣ d³.
      have h₃ : a ∣ a * (b * 16) := by
        apply dvd_mul_right
      rw [<-h₀, mul_sub] at h₃
      have h₄ : a ∣ d ^ 3 * a ^ 5 := by
        rw [show a ^ 5 = a ^ 4 * a by ring_nf, <-mul_assoc]
        apply dvd_mul_left
      rw [dvd_iff_dvd_of_dvd_sub h₃] at h₄
      have h₅ : a ∣ d ^ 3 := by
        apply IsCoprime.dvd_of_dvd_mul_right _ h₄
        apply IsCoprime.pow_right
        rw [Int.isCoprime_iff_gcd_eq_one]
        exact h₂
      -- Similarly, b ∣ d³a⁵ and hence b ∣ d³.
      have h₆ : b ∣ b * (a * 16) := by
        apply dvd_mul_right
      rw [show b * (a * 16) = a * (b * 16) by ac_rfl, <-h₀, mul_sub] at h₆
      have h₇ : b ∣ d ^ 3 * b ^ 5 := by
        rw [show b ^ 5 = b ^ 4 * b by ring_nf, <-mul_assoc]
        apply dvd_mul_left
      rw [<-dvd_iff_dvd_of_dvd_sub h₆] at h₇
      have h₈ : b ∣ d ^ 3 := by
        rw [mul_comm] at h₆
        apply IsCoprime.dvd_of_dvd_mul_right _ h₇
        apply IsCoprime.pow_right
        rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
        exact h₂
      -- Show that ab divides d³.
      have h₉ : a * b ∣ d ^ 3 := by
        apply IsCoprime.mul_dvd
        rw [Int.isCoprime_iff_gcd_eq_one, h₂]
        exact h₅
        exact h₈
      -- Show that d³ = abr for some r ∈ ℤ.
      obtain ⟨r, h₉⟩ := h₉
      -- Substitute d³ by abr.
      rw [h₉, <-mul_assoc, mul_assoc (a * b)] at h₀
      -- We have r(a⁵ - b⁵) = 16.
      have : a * b ≠ 0 := by
        by_contra!
        simp at this
        rcases this with (this | this)
        <;> simp_all
      rw [Int.mul_eq_mul_left_iff this] at h₀
      clear this
      -- Show that a⁵ - b⁵ ∣ 16.
      have h₁₀ : a ^ 5 - b ^ 5 ∣ 16 := by
        rw [<-h₀]
        apply dvd_mul_left
      rw [<-Int.natAbs_dvd_natAbs] at h₁₀
      simp at h₁₀
      replace h₁₀ : (a ^ 5 - b ^ 5).natAbs ∣ 16 ∧ 16 ≠ 0 := by
        exact ⟨h₁₀, by norm_num⟩
      rw [<-Nat.mem_divisors] at h₁₀
      -- Use the computer to find the factors of 16 (native_decide is necessary).
      rw [show Nat.divisors 16 = {1, 2, 4, 8, 16} by native_decide] at h₁₀
      simp at h₁₀
      -- Subtle lemma showing (m + 1)⁵ - x⁵ = 5x⁴ + 10x³ + 10x² + 5x + 1.
      have lemma₁ (m : ℤ) : (m + 1) ^ 5 - m ^ 5 = 1 + m * 5 + m ^ 2 * 10 + m ^ 3 * 10 + m ^ 4 * 5 := by
        ring
      -- Subtle lemma showing (m + 2)⁵ - x⁵ = 10x⁴ + 40x³ + 80x² + 80x + 32.
      have lemma₂ (m : ℤ) : (m + 2) ^ 5 - m ^ 5 = 32 + m * 80 + m ^ 2 * 80 + m ^ 3 * 40 + m ^ 4 * 10 := by
        ring
      clear h₃ h₄ h₅ h₆ h₇ h₈
      -- Separate the cases |a⁵ - b⁵| = 1, 2, 4, 8, 16.
      obtain hab | hab | hab | hab | hab := h₁₀
      . -- Deal with the case |a⁵ - b⁵| = 1.
        have hab' := hab
        rw [show a ^ 5 - b ^ 5 = (a - b) * (a ^ 4 + a ^ 3 * b + a ^ 2 * b ^ 2 + a * b ^ 3 + b ^ 4) by ring] at hab'
        rw [Int.natAbs_mul] at hab'
        -- We have |a - b| = 1 and |a⁴ + a³b + a²b² + ab³ + b⁴| = 1.
        simp at hab'
        replace hab' := hab'.1
        rw [Int.natAbs_eq_iff] at hab'
        simp at hab'
        -- We have a⁵ - b⁵ = ±1.
        simp [Int.natAbs_eq_iff] at hab
        obtain hab | hab := hab
        . -- Prove by contradiction that a ≥ b, so a - b = 1.
          have g₀ : a ≥ b := by
            by_contra!
            replace this : a ^ 5 < b ^ 5 := by
              apply Odd.strictMono_pow
              trivial
              exact this
            omega
          simp [show a - b ≠ -1 by omega] at hab'
          -- Consider cases a ≥ 2.
          by_cases g₁ : a ≥ 2
          . -- Change a - b = 1 to a = b + 1, and then substitute into hab.
            apply eq_add_of_sub_eq at hab'
            rw [add_comm] at hab'
            rw [hab'] at hab
            rw [lemma₁] at hab
            -- Show that b ≥ 1.
            have g₂ : b ≥ 1 := by
              omega
            -- Show that 1 < 1 + 5b + ..., and hence a contradiction could be derived.
            absurd hab
            apply ne_of_gt
            calc
              1 < 1 + b * 5 := by omega
              _ ≤ 1 + b * 5 + b ^ 2 * 10 + b ^ 3 * 10 + b ^ 4 * 5 := by
                rw [add_assoc, add_assoc]
                apply Int.le_add_of_nonneg_right
                positivity
          . -- Consider case a ≤ -1.
            by_cases g₂ : a ≤ -1
            . -- Change hab to (-a + 1)⁵ - (-a)⁵ = 1.
              replace hab : (-a + 1) ^ 5 - (-a) ^ 5 = 1 := by
                rw [show -a + 1 = -b by linarith only [hab'], Int.neg_eq_neg_one_mul, mul_pow, Int.neg_eq_neg_one_mul a, mul_pow]
                linarith only [hab]
              rw [lemma₁] at hab
              -- Show that 1 < 1 + 5(-a) + ..., and hence a contradiction could be derived.
              absurd hab
              apply ne_of_gt
              calc
                1 < 1 + -a * 5 := by omega
                _ ≤ 1 + -a * 5 + (-a) ^ 2 * 10 + (-a) ^ 3 * 10 + (-a) ^ 4 * 5 := by
                  let a' := (-a : ℤ)
                  rw [show -a = a' by simp [a'], add_assoc, add_assoc]
                  apply Int.le_add_of_nonneg_right
                  replace g₂ : -a ≥ 1 := by omega
                  positivity
            . -- Consider case -1 < a < 2.
              interval_cases a
              . -- Case a = 0. Contradiction since m = 0.
                omega
              . -- Case a = 1. Contradiction since n = 0.
                rw [show b = 0 by omega] at hy
                omega
        . -- Prove by contradiction that a ≤ b, so a - b = -1.
          have g₀ : a ≤ b := by
            by_contra!
            replace this : b ^ 5 < a ^ 5 := by
              apply Odd.strictMono_pow
              trivial
              exact this
            omega
          simp [show a - b ≠ 1 by omega] at hab'
          -- Consider cases b ≥ 2.
          by_cases g₁ : b ≥ 2
          . -- Change a - b = -1 to b = a + 1, and then substitute into hab.
            replace hab' : b = a + 1 := by
              linarith only [hab']
            replace hab : b ^ 5 - a ^ 5 = 1 := by
              linarith only [hab]
            rw [hab'] at hab
            rw [lemma₁] at hab
            -- Show that a ≥ 1.
            have g₂ : a ≥ 1 := by
              omega
            -- Show that 1 < 1 + 5a + ..., and hence a contradiction could be derived.
            absurd hab
            apply ne_of_gt
            calc
              1 < 1 + a * 5 := by omega
              _ ≤ 1 + a * 5 + a ^ 2 * 10 + a ^ 3 * 10 + a ^ 4 * 5 := by
                rw [add_assoc, add_assoc]
                apply Int.le_add_of_nonneg_right
                positivity
          . -- Consider case b ≤ -1.
            by_cases g₂ : b ≤ -1
            . -- Change hab to (-b + 1)⁵ - (-b)⁵ = 1.
              replace hab : (-b + 1) ^ 5 - (-b) ^ 5 = 1 := by
                rw [show -b + 1 = -a by linarith only [hab'], Int.neg_eq_neg_one_mul, mul_pow, Int.neg_eq_neg_one_mul b, mul_pow]
                linarith only [hab]
              rw [lemma₁] at hab
              -- Show that 1 < 1 + 5(-b) + ..., and hence a contradiction could be derived.
              absurd hab
              apply ne_of_gt
              calc
                1 < 1 + -b * 5 := by omega
                _ ≤ 1 + -b * 5 + (-b) ^ 2 * 10 + (-b) ^ 3 * 10 + (-b) ^ 4 * 5 := by
                  let b' := (-b : ℤ)
                  rw [show -b = b' by simp [b'], add_assoc, add_assoc]
                  apply Int.le_add_of_nonneg_right
                  replace g₂ : -b ≥ 1 := by omega
                  positivity
            . -- Consider case -1 < b < 2.
              interval_cases b
              . -- Case b = 0. Contradiction since n = 0.
                omega
              . -- Case b = 1. Contradiction since m = 0.
                rw [show a = 0 by omega] at hx
                omega
      . -- Deal with the case |a⁵ - b⁵| = 2.
        have hab' := hab
        rw [show a ^ 5 - b ^ 5 = (a - b) * (a ^ 4 + a ^ 3 * b + a ^ 2 * b ^ 2 + a * b ^ 3 + b ^ 4) by ring] at hab'
        rw [Int.natAbs_mul] at hab'
        have hab'' := hab'
        -- We have |a - b| = 1 or 2.
        replace hab' : Int.natAbs (a - b) ≤ 2 := by
          rw [<-hab']
          apply Nat.le_mul_of_pos_right
          by_contra!
          simp at this
          simp [this] at hab'
        replace hab' : Int.natAbs (a - b) = 1 ∨ Int.natAbs (a - b) = 2 := by
          interval_cases Int.natAbs (a - b)
          . simp at hab''
          . trivial
          . trivial
        -- We have a⁵ - b⁵ = ±2.
        rw [Int.natAbs_eq_iff] at hab
        norm_cast at hab
        rw [show Int.negSucc 1 = -2 by norm_cast] at hab
        cases hab' with
        | inl hab' =>
          -- We have |a - b| = 1 and |a⁴ + a³b + a²b² + ab³ + b⁴| = 2.
          simp [hab'] at hab''
          rw [Int.natAbs_eq_iff] at hab'
          simp at hab'
          obtain hab | hab := hab
          . -- Prove by contradiction that a ≥ b, so a - b = 1.
            have g₀ : a ≥ b := by
              by_contra!
              replace this : a ^ 5 < b ^ 5 := by
                apply Odd.strictMono_pow
                trivial
                exact this
              omega
            simp [show a - b ≠ -1 by omega] at hab'
            -- Consider cases a ≥ 2.
            by_cases g₁ : a ≥ 2
            . -- Change a - b = 1 to a = b + 1, and then substitute into hab.
              apply eq_add_of_sub_eq at hab'
              rw [add_comm] at hab'
              rw [hab'] at hab
              rw [lemma₁] at hab
              -- Show that b ≥ 1.
              have g₂ : b ≥ 1 := by
                omega
              -- Show that 2 < 1 + 5b + ..., and hence a contradiction could be derived.
              absurd hab
              apply ne_of_gt
              calc
                2 < 1 + b * 5 := by omega
                _ ≤ 1 + b * 5 + b ^ 2 * 10 + b ^ 3 * 10 + b ^ 4 * 5 := by
                  rw [add_assoc, add_assoc]
                  apply Int.le_add_of_nonneg_right
                  positivity
            . -- Consider case a ≤ -1.
              by_cases g₂ : a ≤ -1
              . -- Change hab to (-a + 1)⁵ - (-a)⁵ = 2.
                replace hab : (-a + 1) ^ 5 - (-a) ^ 5 = 2 := by
                  rw [show -a + 1 = -b by linarith only [hab'], Int.neg_eq_neg_one_mul, mul_pow, Int.neg_eq_neg_one_mul a, mul_pow]
                  linarith only [hab]
                rw [lemma₁] at hab
                -- Show that 2 < 1 + 5(-a) + ..., and hence a contradiction could be derived.
                absurd hab
                apply ne_of_gt
                calc
                  2 < 1 + -a * 5 := by omega
                  _ ≤ 1 + -a * 5 + (-a) ^ 2 * 10 + (-a) ^ 3 * 10 + (-a) ^ 4 * 5 := by
                    let a' := (-a : ℤ)
                    rw [show -a = a' by simp [a'], add_assoc, add_assoc]
                    apply Int.le_add_of_nonneg_right
                    replace g₂ : -a ≥ 1 := by omega
                    positivity
              . -- Consider case -1 < a < 2.
                interval_cases a
                . -- Case a = 0. Contradiction since m = 0.
                  omega
                . -- Case a = 1. Contradiction since n = 0.
                  rw [show b = 0 by omega] at hy
                  omega
          . -- Prove by contradiction that a ≤ b, so a - b = -1.
            have g₀ : a ≤ b := by
              by_contra!
              replace this : b ^ 5 < a ^ 5 := by
                apply Odd.strictMono_pow
                trivial
                exact this
              omega
            simp [show a - b ≠ 1 by omega] at hab'
            -- Consider cases b ≥ 2.
            by_cases g₁ : b ≥ 2
            . -- Change a - b = -1 to b = a + 1, and then substitute into hab.
              replace hab' : b = a + 1 := by
                linarith only [hab']
              replace hab : b ^ 5 - a ^ 5 = 2 := by
                linarith only [hab]
              rw [hab'] at hab
              rw [lemma₁] at hab
              -- Show that a ≥ 1.
              have g₂ : a ≥ 1 := by
                omega
              -- Show that 2 < 1 + 5a + ..., and hence a contradiction could be derived.
              absurd hab
              apply ne_of_gt
              calc
                2 < 1 + a * 5 := by omega
                _ ≤ 1 + a * 5 + a ^ 2 * 10 + a ^ 3 * 10 + a ^ 4 * 5 := by
                  rw [add_assoc, add_assoc]
                  apply Int.le_add_of_nonneg_right
                  positivity
            . -- Consider case b ≤ -1.
              by_cases g₂ : b ≤ -1
              . -- Change hab to (-b + 1)⁵ - (-b)⁵ = 2.
                replace hab : (-b + 1) ^ 5 - (-b) ^ 5 = 2 := by
                  rw [show -b + 1 = -a by linarith only [hab'], Int.neg_eq_neg_one_mul, mul_pow, Int.neg_eq_neg_one_mul b, mul_pow]
                  linarith only [hab]
                rw [lemma₁] at hab
                -- Show that 2 < 1 + 5(-b) + ..., and hence a contradiction could be derived.
                absurd hab
                apply ne_of_gt
                calc
                  2 < 1 + -b * 5 := by omega
                  _ ≤ 1 + -b * 5 + (-b) ^ 2 * 10 + (-b) ^ 3 * 10 + (-b) ^ 4 * 5 := by
                    let b' := (-b : ℤ)
                    rw [show -b = b' by simp [b'], add_assoc, add_assoc]
                    apply Int.le_add_of_nonneg_right
                    replace g₂ : -b ≥ 1 := by omega
                    positivity
              . -- Consider case -1 < b < 2.
                interval_cases b
                . -- Case b = 0. Contradiction since n = 0.
                  omega
                . -- Case b = 1. Contradiction since m = 0.
                  rw [show a = 0 by omega] at hx
                  omega
        | inr hab' =>
          -- We have |a - b| = 2 and |a⁴ + a³b + a²b² + ab³ + b⁴| = 1.
          simp [hab'] at hab''
          rw [Int.natAbs_eq_iff] at hab'
          norm_cast at hab'
          rw [show Int.negSucc 1 = -2 by norm_cast] at hab'
          obtain hab | hab := hab
          . -- Prove by contradiction that a ≥ b, so a - b = 2.
            have g₀ : a ≥ b := by
              by_contra!
              replace this : a ^ 5 < b ^ 5 := by
                apply Odd.strictMono_pow
                trivial
                exact this
              omega
            simp [show a - b ≠ -2 by omega] at hab'
            -- Consider cases a ≥ 2.
            by_cases g₁ : a ≥ 2
            . -- Change a - b = 2 to a = b + 2, and then substitute into hab.
              apply eq_add_of_sub_eq at hab'
              rw [add_comm] at hab'
              rw [hab'] at hab
              rw [lemma₂] at hab
              -- Show that b ≥ 0.
              have g₂ : b ≥ 0 := by
                omega
              -- Show that 2 < 32 + ..., and hence a contradiction could be derived.
              absurd hab
              apply ne_of_gt
              calc
                2 < 32 := by norm_num
                _ ≤ 32 + b * 80 + b ^ 2 * 80 + b ^ 3 * 40 + b ^ 4 * 10 := by
                  rw [add_assoc, add_assoc, add_assoc]
                  apply Int.le_add_of_nonneg_right
                  positivity
            . -- Consider case a ≤ -1.
              by_cases g₂ : a ≤ -1
              . -- Change hab to (-a + 2)⁵ - (-a)⁵ = 2.
                replace hab : (-a + 2) ^ 5 - (-a) ^ 5 = 2 := by
                  rw [show -a + 2 = -b by linarith only [hab'], Int.neg_eq_neg_one_mul, mul_pow, Int.neg_eq_neg_one_mul a, mul_pow]
                  linarith only [hab]
                rw [lemma₂] at hab
                -- Show that 2 < 32 + ..., and hence a contradiction could be derived.
                absurd hab
                apply ne_of_gt
                calc
                  2 < 32 := by omega
                  _ ≤ 32 + -a * 80 + (-a) ^ 2 * 80 + (-a) ^ 3 * 40 + (-a) ^ 4 * 10 := by
                    let a' := (-a : ℤ)
                    rw [show -a = a' by simp [a'], add_assoc, add_assoc, add_assoc]
                    apply Int.le_add_of_nonneg_right
                    replace g₂ : -a ≥ 1 := by omega
                    positivity
              . -- Consider case -1 < a < 2.
                interval_cases a
                . -- Case a = 0. Contradiction since m = 0.
                  omega
                . -- Case a = 1. Contradiction since d < 0.
                  rw [show b = -1 by omega] at hy h₀ h₉
                  simp [show r = 8 by omega] at h₉
                  norm_cast at h₉
          . -- Prove by contradiction that a ≤ b, so a - b = -2.
            have g₀ : a ≤ b := by
              by_contra!
              replace this : b ^ 5 < a ^ 5 := by
                apply Odd.strictMono_pow
                trivial
                exact this
              omega
            simp [show a - b ≠ 2 by omega] at hab'
            -- Consider cases b ≥ 2.
            by_cases g₁ : b ≥ 2
            . -- Change a - b = -2 to b = a + 2, and then substitute into hab.
              replace hab' : b = a + 2 := by
                linarith only [hab']
              replace hab : b ^ 5 - a ^ 5 = 2 := by
                linarith only [hab]
              rw [hab'] at hab
              rw [lemma₂] at hab
              -- Show that a ≥ 0.
              have g₂ : a ≥ 0 := by
                omega
              -- Show that 2 < 32 + ..., and hence a contradiction could be derived.
              absurd hab
              apply ne_of_gt
              calc
                2 < 32 := by omega
                _ ≤ 32 + a * 80 + a ^ 2 * 80 + a ^ 3 * 40 + a ^ 4 * 10 := by
                  rw [add_assoc, add_assoc, add_assoc]
                  apply Int.le_add_of_nonneg_right
                  positivity
            . -- Consider case b ≤ -1.
              by_cases g₂ : b ≤ -1
              . -- Change hab to (-b + 2)⁵ - (-b)⁵ = 2.
                replace hab : (-b + 2) ^ 5 - (-b) ^ 5 = 2 := by
                  rw [show -b + 2 = -a by linarith only [hab'], Int.neg_eq_neg_one_mul, mul_pow, Int.neg_eq_neg_one_mul b, mul_pow]
                  linarith only [hab]
                rw [lemma₂] at hab
                -- Show that 2 < 32 + ..., and hence a contradiction could be derived.
                absurd hab
                apply ne_of_gt
                calc
                  2 < 32 := by omega
                  _ ≤ 32 + -b * 80 + (-b) ^ 2 * 80 + (-b) ^ 3 * 40 + (-b) ^ 4 * 10 := by
                    let b' := (-b : ℤ)
                    rw [show -b = b' by simp [b'], add_assoc, add_assoc, add_assoc]
                    apply Int.le_add_of_nonneg_right
                    replace g₂ : -b ≥ 1 := by omega
                    positivity
              . -- Consider case -1 < b < 2.
                interval_cases b
                . -- Case b = 0. Contradiction since n = 0.
                  omega
                . -- Case b = 1. Possible solution (m, n) = (-2, 2).
                  rw [show a = -1 by omega] at hx h₀ h₉
                  simp [show r = -8 by omega] at h₉
                  norm_cast at h₉
                  rw [show 8 = 2 ^ 3 by norm_num] at h₉
                  apply Nat.pow_left_injective (by norm_num) at h₉
                  right
                  rw [h₉] at hx hy
                  norm_num at hx
                  simp
                  tauto
      all_goals
        -- Deal with the case |a⁵ - b⁵| = 4, 8 or 16, and derive a contradiction in each case.
        exfalso
        -- Clear r, otherwise hard to do WLOG.
        clear r h₀ h₉
        -- WLOG, assume that a ≥ b.
        wlog h : a ≥ b
        . -- Prove that the 'WLOG' argument is valid.
          apply this n m
          . exact ⟨h₁.2, h₁.1⟩
          . nth_rewrite 1 [Int.gcd_comm]
            rw [show n.gcd m = d by rw [Int.gcd_comm], show m / d = a by simp [a], show n / d = b by simp [b]]
            exact h₂
          . symm
            apply Int.mul_ediv_cancel_of_emod_eq_zero
            simp
            apply Int.gcd_dvd_left
          . symm
            apply Int.mul_ediv_cancel_of_emod_eq_zero
            simp
            apply Int.gcd_dvd_right
          . exact lemma₁
          . exact lemma₂
          . rw [show n.gcd m = d by rw [Int.gcd_comm], show m / d = a by simp [a], show n / d = b by simp [b]]
            rw [<-Int.neg_sub, Int.natAbs_neg]
            exact hab
          . rw [show n.gcd m = d by rw [Int.gcd_comm], show m / d = a by simp [a], show n / d = b by simp [b]]
            omega
        . -- Assume that a ≥ b.
          replace hab : Int.natAbs (a ^ 5 - b ^ 5) > 2 ∧ Int.natAbs (a ^ 5 - b ^ 5) < 31 := by
            omega
          rw [ge_iff_le] at h
          -- Show that a⁵ ≤ b⁵.
          have h' : b ^ 5 ≤ a ^ 5 := by
            rw [le_iff_eq_or_lt] at h ⊢
            cases h with
            | inl h =>
              rw [h]
              tauto
            | inr h =>
              right
              apply Odd.strictMono_pow
              trivial
              exact h
          zify at hab
          rw [abs_of_nonneg (show 0 ≤ a ^ 5 - b ^ 5 by omega)] at hab
          by_cases g₀ : a ≥ 2
          . -- Consider the case a ≥ 2.
            have g₁ : a ^ 5 - (a - 1) ^ 5 ≥ 31 := by
              let a' := a - 1
              simp [show a = a' + 1 by simp [a']]
              rw [lemma₁, add_assoc, add_assoc]
              have g' : a' ≥ 1 := by
                omega
              have g'' : a' ^ 2 ≥ 1 := by
                nlinarith only [g']
              have g''' : a' ^ 3 ≥ 1 := by
                nlinarith only [g', g'']
              have g'''' : a' ^ 4 ≥ 1 := by
                nlinarith only [g'']
              linarith only [g', g'', g''', g'''']
            -- Show that b > a - 1.
            have g₂ : b ≥ a - 1 := by
              by_contra!
              replace this : b ^ 5 < (a - 1) ^ 5 := by
                apply Odd.strictMono_pow
                trivial
                exact this
              omega
            have g₂ : b ≠ a - 1 := by
              by_contra!
              rw [<-this] at g₁
              omega
            -- Show that b ≠ a, and hence contradiction.
            have g₂ : b ≠ a := by
              by_contra!
              rw [this] at hab
              omega
            omega
          . by_cases g₁ : a ≤ -1
            . -- Consider the case a ≤ -1.
              have g₁ : a ^ 5 - (a - 1) ^ 5 ≥ 31 := by
                let a' := -a
                rw [show a = -a' by simp [a'], <-Int.neg_sub, neg_pow, neg_sub_left, neg_pow]
                simp
                apply Int.add_le_of_le_sub_left
                rw [add_comm, lemma₁]
                have g' : a' ≥ 1 := by
                  omega
                have g'' : a' ^ 2 ≥ 1 := by
                  nlinarith only [g']
                have g''' : a' ^ 3 ≥ 1 := by
                  nlinarith only [g', g'']
                have g'''' : a' ^ 4 ≥ 1 := by
                  nlinarith only [g'']
                linarith only [g', g'', g''', g'''']
              -- Show that b > a - 1.
              have g₂ : b ≥ a - 1 := by
                by_contra!
                replace this : b ^ 5 < (a - 1) ^ 5 := by
                  apply Odd.strictMono_pow
                  trivial
                  exact this
                omega
              have g₂ : b ≠ a - 1 := by
                by_contra!
                rw [<-this] at g₁
                omega
              -- Show that b ≠ a, and hence contradiction.
              have g₂ : b ≠ a := by
                by_contra!
                rw [this] at hab
                omega
              omega
            . -- Consider the case -1 < a < 2.
              interval_cases a
              . -- Case a = 0. Contradiction since m = 0.
                omega
              . -- Case a = 1.
                -- Contradiction when b ≥ -2.
                have g₂ : b ≥ -2 := by
                  by_contra!
                  replace this : b ^ 5 < (-2) ^ 5 := by
                    apply Odd.strictMono_pow
                    trivial
                    exact this
                  omega
                -- Contradiction in any case.
                interval_cases b
                all_goals
                  by_contra!
                  omega
  . -- Show that (m, n) = (0, 0) or (-2, 2) are solutions.
    intro h
    obtain h | h := h
    all_goals
      simp at h
      simp [h.1, h.2]
