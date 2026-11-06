import Mathlib
open Nat Finset

/-
Claim: For every integer M ≥ 6, S_M := M! + (M-1)! + Σ_{k=1}^{M-2} (-1)^(k+1)k!
       has units-digit 1.
-/
theorem units_digit_of_sum_is_one (M : ℕ) (hM : 6 ≤ M) :
  ((M ! : ℤ) + ((M - 1) ! : ℤ) + ∑ k ∈ Ico 1 (M-1), (-1 : ℤ)^(k + 1) * (k ! : ℤ)) ≡ 1 [ZMOD 10] := by

  -- Step 1: For n ≥ 5, n! contains factors 2 and 5, so 10 | n!, meaning n! ≡ 0 [ZMOD 10].
  have factorial_modEq_zero : ∀ (n : ℕ), 5 ≤ n → 10 ∣ n ! := by
    intro n hn
    have : n ! = 120 * ∏ i ∈ Ico 6 (n+1), i:= by
      calc
        _ = ∏ i ∈ Finset.Ico 1 (n + 1), i := by exact Eq.symm (Finset.prod_Ico_id_eq_factorial n)
        _ = (∏ i ∈ Finset.Ico 1 6, i) * (∏ i ∈ Finset.Ico 6 (n + 1), i) := by rw [Finset.prod_Ico_consecutive] <;> omega
        _ = 120 * (∏ i ∈ Finset.Ico 6 (n + 1), i) := by exact rfl

    rw [this]
    refine dvd_gcd_mul_gcd_iff_dvd_mul.mp ?_
    simp


  -- Reduce S_M modulo 10.
  -- S_M = M! + (M-1)! + Σ_{k=1}^{M-2} (-1)ᵏ⁺¹k!
  -- Since M ≥ 6, both M and M-1 are ≥ 5. Thus M! ≡ 0 and (M-1)! ≡ 0 [ZMOD 10].

  have h_sum_1 : ∑ k ∈ Ico 1 5, (-1 : ℤ)^(k + 1) * (k ! : ℤ) ≡ 1 [ZMOD 10] := by
    calc
      _ = 1 - 2 + 6 - 24 := by congr
      _ = -19 := by norm_num
      _ ≡ 1 [ZMOD 10] := by decide


  have h_sum_2 : ∑ k ∈ Ico 5 (M-1), (-1 : ℤ)^(k + 1) * (k ! : ℤ) ≡ 0 [ZMOD 10] := by
    let sum_fac := ∑ k ∈ Ico 5 (M-1), (-1 : ℤ)^(k + 1) * (k ! : ℤ)
    have: sum_fac = (0: ZMod 10) := by
      calc
        _ = ∑ k ∈ Ico 5 (M-1), (-1 : ℤ)^(k + 1) * ((k ! : ℤ):ZMod 10) := by simp [sum_fac]
        _ = ∑ k ∈ Ico 5 (M-1), (-1 : ℤ)^(k + 1) * (0:ZMod 10) := by
          apply Finset.sum_congr rfl
          intro k hk
          congr
          norm_cast
          simp only [mem_Ico] at hk
          have : 10 ∣ k ! := factorial_modEq_zero k hk.1
          have : (k ! : ZMod 10) = 0 := by exact (ZMod.natCast_zmod_eq_zero_iff_dvd k ! 10).mpr this
          exact this
        _ = 0 := by norm_num

    apply (ZMod.intCast_eq_intCast_iff sum_fac 0 10).mp
    exact this

  -- The proof proceeds by a chain of congruences using a `calc` block.
  calc
    -- Start with the original expression S_M.
    _ ≡ 0 + 0 + ∑ k ∈ Ico 1 (M-1), (-1 : ℤ)^(k + 1) * (k ! : ℤ) [ZMOD 10] := by
      have h1 : 10 ∣ M ! := factorial_modEq_zero M (by omega)
      have h2 : 10 ∣ (M - 1) ! := factorial_modEq_zero (M - 1) (by omega)
      apply Int.ModEq.add
      · apply Int.ModEq.add
        · refine Dvd.dvd.modEq_zero_int ?_
          exact Int.ofNat_dvd_right.mpr h1
        · refine Dvd.dvd.modEq_zero_int ?_
          exact Int.ofNat_dvd_right.mpr h2
      · rfl
      -- Step 2: Reduce S_M modulo 10.
      -- Since M ≥ 6, both M! and (M-1)! are congruent to 0.
    _ ≡ ∑ k ∈ Ico 1 (M-1), (-1 : ℤ)^(k + 1) * (k ! : ℤ) [ZMOD 10]:= by simp
      -- Simplify the expression by removing the zeros.

    _ ≡ ∑ k ∈ Ico 1 5, (-1 : ℤ)^(k + 1) * (k ! : ℤ) + ∑ k ∈ Ico 5 (M-1), (-1 : ℤ)^(k + 1) * (k ! : ℤ) [ZMOD 10] := by rw [Finset.sum_Ico_consecutive] <;> omega
      -- For k ≥ 5, the term k! is 0 mod 10, so the sum from k=5 onwards is 0.
    _ ≡ 1 + 0 [ZMOD 10] := by apply Int.ModEq.add h_sum_1 h_sum_2
    _ = 1 := by simp
