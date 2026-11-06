import Mathlib

open Finset

/- For how many integers $1 \leq k \leq 2013$ does the decimal representation of $k^{k}$ end with a 1 ? -/
theorem number_theory_609109 :
    #{k ∈ Finset.Icc 1 2013 | k ^ k ≡ 1 [MOD 10]} = 202 := by
  -- The condition k ^ k ≡ 1 [MOD 10] is equivalent to k = 0 ∨ k ≡ 1 [MOD 10]
  -- We first show that if the equivalence holds, then the original statement holds
  suffices H : ∀ k, k ^ k ≡ 1 [MOD 10] ↔ k = 0 ∨ k ≡ 1 [MOD 10] by
    -- We rewrite the condition to k = 0 ∨ k ≡ 1 [MOD 10]
    simp [H]
    -- We show that 10 * s + 1 establishes a bijection between {0, 1, ..., 202-1} and the set of integers k ∈ [1, 2013] such that k = 0 (never happens) ∨ k ^ k ≡ 1 [MOD 10]
    apply Finset.card_eq_of_bijective (fun s _ ↦ 10 * s + 1)
    . simp
      intro a h₁ h₂ h₃
      rcases h₃ with rfl | h₃
      {
        simp at h₁
      }
      simp [Nat.ModEq] at h₃
      use a / 10
      omega
    . simp [Nat.ModEq]
      intro i hi
      omega
    . simp
  -- We now show that the equivalence holds
  intro k
  constructor
  swap
  {
    rintro (rfl | h)
    -- If k = 0, then k ^ k = 0, which is not congruent to 1 modulo 10
    . simp [Nat.ModEq]
    -- If k ≡ 1 [MOD 10], then k = 1 as a member of ZMod 10
    -- So k ^ k = 1 ^ 1 = 1 in ZMod 10
    . replace h : (k : ZMod 10) = 1 := (ZMod.natCast_eq_natCast_iff' k 1 10).mpr h
      apply (ZMod.natCast_eq_natCast_iff' (k ^ k) 1 10).mp
      simp [h]
  }
  -- We now suppose that k > 0 and k ^ k ≡ 1 [MOD 10]
  intro h
  wlog hk : k > 0
  {
    simp at hk
    simp [hk]
  }
  -- We will prove that k ≡ 1 [MOD 10]
  right
  -- First, we show that k is coprime to 10
  have h₁ : k.Coprime 10 := by
    -- Which is implied by k ^ k ≡ 1 [MOD 10]
    suffices H : (k ^ k).Coprime 10 from (Nat.coprime_pow_left_iff hk k 10).mp H
    -- So gcd(k^k, 10) = gcd(1, 10) = 1
    simp [Nat.Coprime, Nat.ModEq.gcd_eq h]
  -- We need to show that k = 1 as a member of ZMod 10
  apply (ZMod.natCast_eq_natCast_iff' k 1 10).mp
  -- And we can show that k is either 1, 3, 7, or 9 in ZMod 10
  have h₂ : k = (1 : ZMod 10) ∨ k = (3 : ZMod 10) ∨ k = (7 : ZMod 10) ∨ k = (9 : ZMod 10) := by
    -- Because k is a unit in ZMod 10
    rw [← ZMod.isUnit_iff_coprime] at h₁
    -- Denote a = k mod 10
    generalize (k : ZMod 10) = a at h₁
    clear k h hk
    -- We do casework on a
    fin_cases a <;> simp at *
    -- a = 0, 2, 4, 5, 6, 8 are not possible
    all_goals
      absurd h₁
      decide
  -- k is odd because gcd(k, 10) = 1, so k = 2s + 1 for some s
  have ⟨s, hs⟩ : Odd k := by
    apply Nat.Coprime.odd_of_right
    exact Nat.Coprime.coprime_mul_right_right h₁ (k := 5)
  rw [Nat.ModEq, ← ZMod.natCast_eq_natCast_iff'] at h
  simp at h
  nth_rw 2 [hs] at h
  -- Now we will show that a ^ (2s + 1) = 1 as a member of ZMod 10 implies a = 1 for any a ∈ {1, 3, 7, 9}, s ∈ ℕ
  generalize (k : ZMod 10) = a at h h₂
  clear k hk h₁ hs
  rcases h₂ with rfl | rfl | rfl | rfl
  -- a = 1
  . simp
  -- The other cases are impossible
  all_goals
    absurd h
    clear h
  . -- a = 3, s = 2t or 2t+1
    obtain ⟨t, rfl⟩ | ⟨t, rfl⟩ := Nat.even_or_odd s
    . -- s = 2t
      -- a ^ (2s+1) = 3 * 81 ^ t = 3 mod 10
      ring_nf
      rw [mul_comm t 4, pow_mul,
          show (3 ^ 4 : ZMod 10) = 1 by decide]
      simp
      decide
    . -- s = 2t+1
      -- a ^ (2s+1) = 27 * 81 ^ t = 7 mod 10
      ring_nf
      rw [mul_comm t 4, pow_mul,
          show (3 ^ 4 : ZMod 10) = 1 by decide]
      simp
      decide
  . -- a = 7, s = 2t or 2t+1
    obtain ⟨t, rfl⟩ | ⟨t, rfl⟩ := Nat.even_or_odd s
    . -- s = 2t
      -- a ^ (2s+1) = 7 * 81 ^ t = 7 mod 10
      ring_nf
      rw [mul_comm t 4, pow_mul,
          show (7 ^ 4 : ZMod 10) = 1 by decide]
      simp
      decide
    . -- s = 2t+1
      -- a ^ (2s+1) = 343 * 81 ^ t = 3 mod 10
      ring_nf
      rw [mul_comm t 4, pow_mul,
          show (7 ^ 4 : ZMod 10) = 1 by decide]
      simp
      decide
  . -- a = 9
    -- a ^ (2s+1) = 9 * 81 ^ s = 9 mod 10
    ring_nf
    rw [mul_comm s 2, pow_mul,
        show (9 ^ 2 : ZMod 10) = 1 by decide]
    simp
    decide
