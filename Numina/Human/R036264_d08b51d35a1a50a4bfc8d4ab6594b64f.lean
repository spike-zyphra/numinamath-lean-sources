import Mathlib

/- What is the sum of all four-digit numbers that are equal to the cube of the sum of their digits (leading zeros are not allowed)?-/
theorem number_theory_608748 :
    ∃ S : Finset ℕ, {n : ℕ | ∃ a b c d : ℕ, 0 ≠ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ d ≤ 9 ∧ n = 1000 * a + 100 * b + 10 * c + d ∧ n = (a + b + c + d) ^ 3} = S ∧ S.sum (λ x => x) = 10745 := by
  -- Use S = {4913, 5832}.
  use {4913, 5832}
  refine ⟨?_, by simp⟩
  ext n
  simp
  -- Break the goal into two parts.
  apply Iff.intro
  . -- First show that the conditions implies that n = 4913 or 5832.
    rintro ⟨a, ha', ha, b, hb, c, hc, d, hd, h₀, h₁⟩
    -- Let k = a + b + c + d.
    let k := a + b + c + d
    -- Show that k³ ≡ k (mod 9).
    have h₂ : k ^ 3 ≡ k [MOD 9] := by
      simp [k]
      calc
        (a + b + c + d) ^ 3 = 1000 * a + 100 * b + 10 * c + d := h₁.symm ▸ h₀
        _ ≡ a + b + c + d [MOD 9] := by
          iterate 3 apply Nat.ModEq.add
          . -- We have 1000a ≡ a (mod 9).
            rw [show 1000 * a = a + 9 * (111 * a) by ring]
            symm
            rw [Nat.modEq_iff_dvd', Nat.add_comm, Nat.add_sub_cancel]
            apply Nat.dvd_mul_right
            omega
          . -- We have 100b ≡ b (mod 9).
            rw [show 100 * b = b + 9 * (11 * b) by ring]
            symm
            rw [Nat.modEq_iff_dvd', Nat.add_comm, Nat.add_sub_cancel]
            apply Nat.dvd_mul_right
            omega
          . -- We have 10c ≡ c (mod 9).
            rw [show 10 * c = c + 9 * c by ring]
            symm
            rw [Nat.modEq_iff_dvd', Nat.add_comm, Nat.add_sub_cancel]
            apply Nat.dvd_mul_right
            omega
          . rfl
    -- Show that k ≡ 0, 1 or 8 (mod 9).
    have h₃ : k % 9 = 0 ∨ k % 9 = 1 ∨ k % 9 = 8 := by
      rw [Nat.ModEq.eq_1, Nat.pow_mod] at h₂
      have h₃ : k % 9 < 9 := by
        apply Nat.mod_lt _ (by norm_num)
      interval_cases k % 9
      all_goals
        omega
    -- Show that 10 ≤ k.
    have h₄ : 10 ^ 3 ≤ k ^ 3 := by
      simp [k]
      rw [<-h₁, h₀]
      omega
    rw [Nat.pow_le_pow_iff_left (by norm_num)] at h₄
    -- Show that k < 22.
    have h₅ : k < 22 := by
      by_contra!
      have : n > n := by
        calc
          n = k ^ 3 := h₁
          _ ≥ 22 ^ 3 := by
            rw [ge_iff_le, Nat.pow_le_pow_iff_left (by norm_num)]
            exact this
          _ > n := by
            omega
      absurd this
      simp
    -- Show that k = 10, 17, 18 or 19.
    have h₆ : k = 10 ∨ k = 17 ∨ k = 18 ∨ k = 19 := by
      omega
    -- Verify each cases.
    rcases h₆ with (h₆ | h₆ | h₆ | h₆)
    . -- Case k = 10, then n = 1000, not satisfying the original equation.
      simp [k] at h₆
      simp [h₆] at h₁
      replace ha : a = 1 := by
        omega
      replace hb : b = 0 := by
        omega
      replace hc : c = 0 := by
        omega
      replace hd : d = 0 := by
        omega
      simp [ha, hb, hc, hd] at h₆
    . -- Case k = 17, then n = 4913.
      simp [k] at h₆
      simp [h₆] at h₁
      tauto
    . -- Case k = 18, then n = 5832.
      simp [k] at h₆
      simp [h₆] at h₁
      tauto
    . -- Case k = 19, then n = 6859, not satisfying the original equation.
      simp [k] at h₆
      simp [h₆] at h₁
      replace ha : a = 6 := by
        omega
      replace hb : b = 8 := by
        omega
      replace hc : c = 5 := by
        omega
      replace hd : d = 9 := by
        omega
      simp [ha, hb, hc, hd] at h₆
  . -- Next show that n = 4913 or 5832 implies the conditions.
    rintro (h | h)
    . -- Show that 4913 satisfies the conditions.
      use 4, by norm_num, by norm_num, 9, by norm_num, 1, by norm_num, 3
      norm_num [h]
    . -- Show that 5832 satisfies the conditions.
      use 5, by norm_num, by norm_num, 8, by norm_num, 3, by norm_num, 2
      norm_num [h]
