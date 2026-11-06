import Mathlib
set_option maxHeartbeats 300000
/- Let $a, b, c$ and $d$ be prime numbers such that $a>3 b>6 c>12 d$ and $a^{2}-b^{2}+c^{2}-d^{2}=1749$. Determine all possible values of $a^{2}+b^{2}+c^{2}+d^{2}$.

## Solutions -/
theorem number_theory_241072 :
    {n : ℕ | ∃ a b c d : ℕ, a.Prime ∧ b.Prime ∧ c.Prime ∧ d.Prime ∧ a > 3 * b ∧ 3 * b > 6 * c ∧ 6 * c > 12 * d ∧ a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2 = 1749 ∧ n = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2} = {1999} := by
  -- Break the goal into two parts.
  ext n
  apply Iff.intro
  . -- First show that the condition implies that a² + b² + c² + d² = 1999.
    simp
    intro a ha b hb c hc d hd h₀ h₁ h₂ h₃ h₄
    rw [h₄]
    clear h₄ n
    -- We have d = 2.
    have h₄ : d = 2 := by
      -- Assume on the contrary that d ≠ 2, then all primes a, b, c, d are odd.
      by_contra! hd''
      have hd' : d > 2 := lt_of_le_of_ne (Nat.Prime.two_le hd) hd''.symm
      have hc' : c > 2 := by
        linarith
      have hb' : b > 2 := by
        linarith
      have ha' : a > 2 := by
        linarith
      -- Now a, b, c, d are all odd primes.
      have ha'' := Nat.Prime.odd_of_ne_two ha ha'.ne'
      have hb'' := Nat.Prime.odd_of_ne_two hb hb'.ne'
      have hc'' := Nat.Prime.odd_of_ne_two hc hc'.ne'
      replace hd'' := Nat.Prime.odd_of_ne_two hd hd''
      -- Now a² - b² + c² - d² is even, which is a contradiction.
      replace h₃ := congr_arg (· % 2) h₃
      simp at h₃
      rw [Nat.add_sub_assoc, Nat.add_mod, show a ^ 2 - b ^ 2 = a ^ 2 + b ^ 2 - 2 * b ^ 2 by omega, Nat.sub_mul_mod, show c ^ 2 - d ^ 2 = c ^ 2 + d ^ 2 - 2 * d ^ 2 by omega, Nat.sub_mul_mod, Nat.add_mod (a ^ 2) (b ^ 2), Nat.add_mod (c ^ 2) (d ^ 2)] at h₃
      rw [Nat.pow_mod a, Nat.pow_mod b, Nat.pow_mod c, Nat.pow_mod d] at h₃
      rw [Nat.odd_iff] at ha'' hb'' hc'' hd''
      rw [ha'', hb'', hc'', hd''] at h₃
      norm_num at h₃
      linarith only [show d ^ 2 ≤ c ^ 2 by nlinarith]
      linarith only [show b ^ 2 ≤ a ^ 2 by nlinarith]
      nlinarith
    -- Next we prove that b ≤ 13.
    have h₅ : b ≤ 13 := by
      -- Assume on the contrary that b > 13, we use the inequality a > 3b > 6c > 12d to get a contradiction.
      by_contra!
      have habsurd : 1749 > 1749 := by
        calc
          1749 = a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2 := h₃.symm
          _ > (3 * b) ^ 2 - b ^ 2 + (2 * d) ^ 2 - d ^ 2 := by
            apply Nat.sub_lt_sub_right (by rw [mul_pow, mul_pow]; omega)
            apply Nat.add_lt_add _ (by rw [Nat.pow_lt_pow_iff_left]; linarith; norm_num)
            apply Nat.sub_lt_sub_right (by nlinarith)
            nlinarith
          _ = 8 * b ^ 2 + 3 * 2 ^ 2 := by
            rw [Nat.add_sub_assoc, mul_pow, mul_pow, <-Nat.sub_one_mul, <-Nat.sub_one_mul, h₄]
            norm_num
            rw [mul_pow]
            omega
          _ ≥ 8 * 15 ^ 2 + 3 * 2 * 2 := by
            apply Nat.add_le_add
            apply Nat.mul_le_mul_left
            rw [Nat.pow_le_pow_iff_left]
            by_contra!
            replace this : b = 14 := by
              omega
            norm_num [this] at hb
            all_goals
              norm_num
          _ > 1749 := by
            norm_num
      absurd habsurd
      norm_num
    -- Show that c = 5.
    have h₆ : c = 5 := by
      -- We have 24 < 6c < 39, so c = 5.
      rw [h₄] at h₂
      replace h₁ : 6 * c < 39 := by
        linarith
      have h₆ : c = 5 ∨ c = 6 := by
        omega
      by_contra!
      simp [this] at h₆
      norm_num [h₆] at hc
    -- Show that b > 10.
    have h₇ : b > 10 := by
      -- Use the fact that 6c < 3b, note that c = 5 now.
      linarith
    -- Show that b ≠ 13.
    have h₈ : b ≠ 13 := by
      -- Assume on the contrary that b = 13, then a² - b² + c² - d² = 1749 implies a² = 1897.
      by_contra!
      simp [this, h₆, h₄] at h₃
      rw [Nat.sub_eq_iff_eq_add (by nlinarith)] at h₃
      -- We have 43² < a² < 44², impossible.
      linarith only [show 43 < a by nlinarith, show a < 44 by nlinarith]
    -- Show that b ≠ 12 (obviously).
    have h₉ : b ≠ 12 := by
      by_contra!
      norm_num [this] at hb
    -- Show that b = 11.
    have h₁₀ : b = 11 := by
      -- We have 11 ≤ b < 13 and b ≠ 12, so b = 11.
      omega
    -- Show that a = 43.
    replace h₃ : a ^ 2 = 43 ^ 2 := by
      rw [h₁₀, h₆, h₄] at h₃
      omega
    apply Nat.pow_left_injective (by norm_num) at h₃
    -- Substitute a, b, c and d into the equation to get the desired result.
    simp_all
  . -- Show that a² + b² + c² + d² = 1999 is possible under such constraints.
    simp
    intro hn
    -- Use (a, b, c, d) = (43, 11, 5, 2).
    use 43, by norm_num, 11, by norm_num, 5, by norm_num, 2, by norm_num
    norm_num [hn]
