import Mathlib

open Nat

/--
We show that the unique smallest `n` ending in `6` which, upon moving the final
`6` to the front, triples, is `6*(10^28-1)/29`.
-/
theorem smallest_n :
  let valid_n : ℕ → Prop := fun n ↦
      n % 10 = 6 ∧
      ∃ t k : ℕ,
        n = 10 * k + 6 ∧
        k < 10 ^ t ∧
        6 * 10 ^ t + k = 3 * n;
  let n_val := (6 * (10 ^ 28 - 1)) / 29;
  29 ∣ 6 * (10 ^ 28 - 1) ∧
  valid_n n_val ∧
  ∀ n', valid_n n' → n_val ≤ n' := by
  dsimp only [smallest_n]
  -- introduce definitions
  let valid_n := fun n ↦
      n % 10 = 6 ∧
      ∃ t k : ℕ,
        n = 10 * k + 6 ∧
        k < 10 ^ t ∧
        6 * 10 ^ t + k = 3 * n;
  let n_val := (6 * (10 ^ 28 - 1)) / 29

  have prime_29 : Fact (Nat.Prime 29) := by decide


  -- Fermat's little theorem in ZMod 29
  have h_pow : 10 ^ 28 = (1: ZMod 29) := by
    apply ZMod.pow_card_sub_one_eq_one
    exact Ne.symm (ne_of_beq_false rfl)


  -- Cast ZMod 29 to ℕ
  have h_div : 29 ∣ (10 ^ 28 - 1) := by
    have h_pow2 : (10 ^ 28 - 1: ℕ) = (0: ZMod 29) := by
      simp [h_pow]
      exact rfl
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd (10 ^ 28 - 1) 29).mp h_pow2



  have eq_1: (10 ^ 27 : ZMod 29) * (10 : ZMod 29) = 1 := by
    calc
      (10 ^ 27 : ZMod 29) * (10 : ZMod 29) = (10 : ZMod 29) ^ 28 := by ring
      _ = 1 := h_pow
  have eq_2: (3: ZMod 29) * (10 : ZMod 29) = (1: ZMod 29) := by
    norm_num
    exact rfl

  have h_pow_99 : 10 ^ 27 = (3: ZMod 29) := by
    have h : (10 ^ 27 : ZMod 29) * 10 = (3: ZMod 29) * 10 := by
      rw [eq_1, eq_2]
    haveI : Invertible (10 : ZMod 29) := Units.invertible (ZMod.unitOfCoprime 10 (by decide : Nat.Coprime 10 29))
    exact (mul_left_inj_of_invertible (10: ZMod 29)).mp h



  constructor

  · -- 1) show `valid_n n_val`
    -- `29 ∣ 6 * (10 ^ 28 - 1)`
    have h_dvd : 29 ∣ 6 * (10 ^ 28 - 1) := by
      exact Nat.dvd_gcd_mul_iff_dvd_mul.mp h_div
    exact h_dvd

  · constructor
    . constructor
      . -- 2 show `(6 * (10 ^ 28 - 1) / 29 % 10 = 6`
        norm_num

      . -- 3) show existence of `t` and `k` such that `n_val = 10 * k + 6` and `k < 10 ^ t` and `6 * 10 ^ t + k = 3 * n_val`

        have h_mod : n_val % 10 = 6 := by norm_num
        have h_exists : ∃ t k, n_val = 10 * k + 6 ∧ k < 10 ^ t ∧ 6 * 10 ^ t + k = 3 * n_val := by
          use 27, 6 * (10 ^ 27 - 3) / 29
          constructor
          · -- n_val = 10 * k + 6
            norm_num
          · constructor
            · -- k < 10 ^ t
              norm_num
            · -- 6 * 10 ^ t + k = 3 * n_val
              norm_num
        exact h_exists

    · -- 3) minimality: any `n'` satisfying `valid_n` is ≥ `n_val`
      intro n' hn'
      rcases hn' with ⟨ht, d, k, hk₁, hk₂, hk₃⟩

      -- by case analysis on d: case 1: d = 0, case 2: d > 0
      by_cases h_d : d = 0

      . -- case 1: d = 0
        have h_k: k < 0 := by simp_all
        omega
      . -- case 2: d > 0
        -- rotation equality: 6*10^t + k = 3*(10*k + 6)
        have hrot : 6 * 10 ^ d + k = 3 * (10 * k + 6) := by rw [hk₁] at hk₃; exact hk₃
        -- rearrange to 29*k = 6*(10^d - 3)
        have h29k : 29 * k = 6 * (10 ^ d - 3) := by omega
        -- express k
        have hk : k = (6 * (10 ^ d - 3)) / 29 := by omega

        have h_29_divides : 29 ∣ (10 ^ d - 3) := by omega

        have h_mod_29: (10 ^ d - 3: ℕ) = (0: ZMod 29):= (ZMod.natCast_zmod_eq_zero_iff_dvd (10 ^ d - 3) 29).mpr h_29_divides

        have h_pow_10_d: 10 ^ d ≥ 3 := by
          calc
            _ ≥ 10 ^ 1 := by exact Nat.le_self_pow h_d (10 ^ 1)
            _ ≥ 3 := by norm_num

        have h_mod_29_pow: 10 ^ d = (3: ZMod 29) := by
          have: 10 ^ d - (3: ZMod 29) = 0 := by
            rw [<-h_mod_29]
            rw [Nat.cast_sub, Nat.cast_pow]
            simp [h_pow_10_d]
            exact h_pow_10_d

          exact eq_of_sub_eq_zero this

        have : 10 ^ d = (10: ZMod 29) ^ 27 := by exact h_mod_29_pow

        -- -- prove d ≥ 27 via orders in ZMod 29
        -- have hmod : (10 : ZMod 29) ^ d = 3 := by
        --   simpa [ZMod.val_natCast, ZMod.val_sub, ZMod.val_mul] using congrArg (ZMod.mk _)
        --     (by simpa [mul_comm] using h29k)

        have hpow : (10 : ZMod 29) ^ (d + 1) = 1 := by
          calc
            _ = 10 * (10 : ZMod 29) ^ d := by ring
            _ = 10 * 3               := by simp [h_mod_29_pow]
            _ = 1                   := by exact h_pow

        let r := orderOf (10 : ZMod 29)

        have h_order_28 : ∀ p, Nat.Prime p → p ∣ 28 → (10:ZMod 29)^ (28/p) ≠ 1 := by
          intro p hp hdiv
          -- since p ∣ 28, p can only belong to 20.primeFactors
          have h_prime_factors : p ∈ ({2, 7} : Finset ℕ) := by
            rw [show ({2, 7} : Finset ℕ) = Nat.primeFactors 28 by native_decide]
            apply Nat.mem_primeFactors.mpr
            exact ⟨hp, by omega, by omega⟩

          simp only [Finset.mem_insert, Finset.mem_singleton] at h_prime_factors
          rcases h_prime_factors with (h2 | h7)
          · -- case p = 2
            have : 28/p = 14 := by rw [h2]
            rw [this]
            exact Ne.symm (ne_of_beq_false rfl)
          · -- case p = 7
            have : 28/p = 4 := by rw [h7]
            rw [this]
            exact Ne.symm (ne_of_beq_false rfl)

        have order_28 : r = 28 := orderOf_eq_of_pow_and_pow_div_prime (by positivity) h_pow h_order_28

        have hdiv : r ∣ (d + 1) := by simpa using orderOf_dvd_of_pow_eq_one hpow

        have hlen : d + 1 ≥ 28 := by exact Nat.le_of_dvd (by norm_num) (order_28 ▸ hdiv)
        have hd : d ≥ 27 := by linarith
        -- monotonicity: 10^t - 3 ≥ 10^27 - 3
        have hmono : 10 ^ d - 3 ≥ 10 ^ 27 - 3 := by
          have h1 : d ≥ 27 := by exact hd
          have h2 : 10 > 0 := by decide
          have h3 : 10 ^ d ≥ 10 ^ 27 := by
            apply Nat.pow_le_pow_right h2 h1
          exact Nat.sub_le_sub_right h3 3
        -- conclude n' ≥ n_val
        calc
          n' = 10 * k + 6                                 := by rw [hk₁]
          _  = 10 * ((6 * (10 ^ d - 3)) / 29) + 6         := by rw [hk]
          _  ≥ 10 * ((6 * (10 ^ 27 - 3)) / 29) + 6         := by omega
          _  = (6 * (10 ^ 28 - 1)) / 29                    := by omega

