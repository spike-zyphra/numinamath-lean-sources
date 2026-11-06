import Mathlib

/- Trouver tous les couples d'entiers strictement positifs ( $\mathrm{m}, \mathfrak{n}$ ) pour lesquels:

$$
1+2^{n}+3^{n}+4^{n}=10^{m}
$$ -/
theorem number_theory_607289 :
    {(m, n) : ℕ × ℕ | 0 < m ∧ 0 < n ∧ 1 + 2 ^ n + 3 ^ n + 4 ^ n = 10 ^ m} = {(1, 1), (2, 3)} := by
  -- Break the goal into two parts.
  ext ⟨m, n⟩
  apply Iff.intro
  . -- First show that the equation implies the two solutions.
    intro h
    simp at h
    obtain ⟨hm, hn, h₀⟩ := h
    -- Analyze the equation modulo 3 to show that n is odd.
    have h₁ : Odd n := by
      have h₁ := congr_arg (· % 3) h₀
      simp at h₁
      rw [Nat.add_mod] at h₁
      nth_rw 2 [Nat.add_mod] at h₁
      nth_rw 3 [Nat.add_mod] at h₁
      rw [Nat.pow_mod] at h₁
      nth_rw 2 [Nat.pow_mod] at h₁
      nth_rw 3 [Nat.pow_mod] at h₁
      nth_rw 4 [Nat.pow_mod] at h₁
      simp [Nat.zero_pow hn] at h₁
      -- If n is even, then 2 ^ n + 4 ^ n ≡ 1 [MOD 3], which is a contradiction.
      by_contra!
      simp at this
      rw [even_iff_two_dvd, dvd_iff_exists_eq_mul_right] at this
      obtain ⟨k, hk⟩ := this
      rw [hk] at h₁
      rw [Nat.pow_mul, add_comm, <-Nat.add_assoc, Nat.add_mod, Nat.pow_mod] at h₁
      norm_num at h₁
    -- Now we have n = 2k + 1 for some k.
    simp [Odd] at h₁
    obtain ⟨k, h₁⟩ := h₁
    -- We show that n < 3 or m < 3.
    have h₂ : n < 3 ∨ m < 3 := by
      -- Assume on the contrary that n ≥ 3 and m ≥ 3. We analyze the equation modulo 8 to get a contradiction.
      by_contra!
      have h₂ := congr_arg (· % 8) h₀
      simp at h₂
      rw [Nat.add_mod] at h₂
      nth_rw 2 [Nat.add_mod] at h₂
      nth_rw 3 [Nat.add_mod] at h₂
      -- Since n ≥ 3, 2 ^ n % 8 = 0.
      obtain ⟨h₃, h₄⟩ := this
      obtain ⟨n', h₃⟩ := Nat.exists_eq_add_of_le' h₃
      obtain ⟨m', h₄⟩ := Nat.exists_eq_add_of_le' h₄
      rw [h₃, h₄] at h₂
      nth_rw 1 [Nat.pow_add] at h₂
      nth_rw 2 [Nat.pow_add] at h₂
      rw [<-h₃, Nat.pow_add, Nat.mul_mod] at h₂
      nth_rw 2 [Nat.mul_mod] at h₂
      nth_rw 3 [Nat.mul_mod] at h₂
      norm_num at h₂
      -- A contradiction is derived from 1 + 3^n ≡ 0 [MOD 8], because n is odd.
      rw [h₁, Nat.pow_add, Nat.add_mod, Nat.mul_mod, Nat.pow_mul, Nat.pow_mod] at h₂
      norm_num at h₂
    -- Now we need only to check each cases.
    cases h₂ with
    | inl h₂ =>
      -- Suppose n < 3.
      interval_cases n
      . -- Case n = 1. We have m = 1.
        rw [show 1 + 2 ^ 1 + 3 ^ 1 + 4 ^ 1 = 10 ^ 1 by norm_num] at h₀
        apply Nat.pow_right_injective at h₀
        simp [h₀]
        norm_num
      . norm_num at h₀
        -- We have 30 = 10^m, no solution, otherwise 1 < m < 2.
        have h₃ : 1 < m := by
          rw [<-@Nat.pow_lt_pow_iff_right 10, <-h₀]
          norm_num
          norm_num
        have h₃ : m < 2 := by
          rw [<-@Nat.pow_lt_pow_iff_right 10, <-h₀]
          norm_num
          norm_num
        omega
    | inr h₂ =>
      -- Suppose m < 3.
      interval_cases m
      . -- Case m = 1. We have n = 1 as considered above.
        have h₃ : n = 1 := by
          -- Assume on the contrary that n ≠ 1, then n ≥ 2.
          by_contra!
          have h₃ : n ≥ 2 := by
            omega
          have h₄ : 10 ^ 1 > 10 ^ 1 := by
            calc
              10 ^ 1 = 1 + 2 ^ n + 3 ^ n + 4 ^ n := h₀.symm
              _ ≥ 1 + 2 ^ 2 + 3 ^ 2 + 4 ^ 2 := by
                apply Nat.add_le_add
                apply Nat.add_le_add
                apply Nat.add_le_add_left
                rw [Nat.pow_le_pow_iff_right]
                exact h₃
                norm_num
                rw [Nat.pow_le_pow_iff_right]
                exact h₃
                norm_num
                rw [Nat.pow_le_pow_iff_right]
                exact h₃
                norm_num
              _ > 10 ^ 1 := by
                norm_num
          norm_num at h₄
        simp [h₃]
      . -- Case m = 2. We have n = 3.
        -- First we have n ≠ 1, 2 by directly checking.
        have h₃ : ¬(n = 1 ∨ n = 2) := by
          by_contra!
          obtain this | this := this
          all_goals
            norm_num [this] at h₀
        -- Show that n ≥ 4 would give a contradiction.
        have h₃ : n < 4 := by
          by_contra!
          have h₄ : 10 ^ 2 > 10 ^ 2 := by
            calc
              10 ^ 2 = 1 + 2 ^ n + 3 ^ n + 4 ^ n := h₀.symm
              _ ≥ 1 + 2 ^ 4 + 3 ^ 4 + 4 ^ 4 := by
                apply Nat.add_le_add
                apply Nat.add_le_add
                apply Nat.add_le_add_left
                rw [Nat.pow_le_pow_iff_right]
                exact this
                norm_num
                rw [Nat.pow_le_pow_iff_right]
                exact this
                norm_num
                rw [Nat.pow_le_pow_iff_right]
                exact this
                norm_num
              _ > 10 ^ 2 := by
                norm_num
          norm_num at h₄
        -- Therefore n = 3.
        simp [show n = 3 by omega]
  . -- Next show that the two solutions indeed satisfy the equation.
    simp
    intro h
    obtain ⟨hm, hn⟩ | ⟨hm, hn⟩ := h
    all_goals
      norm_num [hm, hn]
