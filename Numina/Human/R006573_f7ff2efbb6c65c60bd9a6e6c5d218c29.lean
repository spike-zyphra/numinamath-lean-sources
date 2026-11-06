import Mathlib

open BigOperators
open ZMod
set_option maxRecDepth 2000

/-
Main theorem statement:
For any even number a > 1, we prove that the sum S of floor divisions a^k/(a+1)
when cast to ZMod(a^2 - 1) equals 1007 * (a-1)
-/
theorem remainder_S_mod (a : ℕ) (ha_even : Even a) (ha_pos : 1 < a) :
  let S := ∑ k ∈ Finset.Ico 1 2015, Nat.div (a^k) (a+1)
  (S : ZMod (a^2 - 1)) = (1007 * (a - 1) : ℕ) := by
  -- Show `a+1` is coprime to `a^2 - 1` so it has an inverse in ZMod
  dsimp only

  -- Define key functions for quotient and remainder
  let q: ℕ → ℕ := fun k => a^k / (a+1)  -- quotient function
  let r: ℕ → ℕ := fun k => a^k % (a+1)  -- remainder function
  let m: ℕ := a + 1                      -- modulus

  -- Basic inequalities and properties needed throughout the proof
  have ha_ge_2: 2 ≤ a := by omega
  have ha_squred_ge_2: 2 ≤ a^2 := by nlinarith
  have h_a_minus_1: (a - 1) / (a - 1) = 1 := Nat.div_self (by omega)
  have h_pos: 0 < a - 1 := by exact Nat.sub_pos_of_lt ha_pos
  have h_le: a - 1 ≤ a^2015 - 1 := by
    gcongr
    nth_rw 1 [←pow_one a]
    exact (pow_le_pow_iff_right₀ (by omega)).mpr (by omega)

  -- Geometric sum helper lemma 1: Relates sum from 1 to m with sum from 0 to m-1
  have geom_sum_1: ∀(x m: ℕ) ,(hm: 1 ≤ m)→(∑ j ∈ Finset.Ico 1 m, x ^ j) = (∑ j ∈ Finset.range m, x ^ j) - 1 := by
    intro x m hm
    have h_sum_two_parts : 1 + ∑ j ∈ Finset.Ico 1 m, x ^ j = ∑ j ∈ Finset.range m, x ^ j:= by
      rw [Finset.range_eq_Ico]
      rw [show 1 = ∑ j ∈ Finset.Ico 0 1, x ^ j by simp]
      apply Finset.sum_Ico_consecutive
      all_goals omega

    have : (∑ j ∈ Finset.Ico 1 m, x ^ j) = (∑ j ∈ Finset.range m, x ^ j) - 1 := by
      exact Nat.eq_sub_of_add_eq' h_sum_two_parts

    rw [this]

  -- Geometric sum helper lemma 2: Relates sum to (x^m - 1)/(x-1)
  have geom_sum_2: ∀(x m: ℕ), (hm: 1 ≤ m) → (hx: 2 ≤ x) → (∑ j ∈ Finset.Ico 1 m, x ^ j) = (x ^ m - 1) / (x - 1) - 1 := by
    intro x m hm hx
    have geom_sum: (∑ j ∈ Finset.range m, x ^ j) = (x ^ m - 1) / (x - 1) := Nat.geomSum_eq hx m
    rw [←geom_sum]
    exact geom_sum_1 x m hm

  -- Remainder properties in modular arithmetic
  have h_r_k: ∀ k, (r k: ZMod (a + 1)).val = r k := by
    intro k
    dsimp only [r]

    calc
      _ = a ^ k % (a + 1) % (a + 1) := by apply ZMod.val_natCast
      _ = a ^ k % (a + 1) := by simp

  -- Key modular arithmetic properties
  have h_a_plus_1: (a + 1: ZMod m) = 0:= by exact natCast_self' a

  have h_a_squared_minus_1: ((a^2 - 1): ZMod (a^2 - 1)) = 0 := by
    have: ((a^2 - 1): ZMod (a^2 - 1)) = ((a^2 - 1): ℕ) := by
        rw [Nat.cast_sub, Nat.cast_pow, Nat.cast_one]
        omega
    rw [this]
    have h_a_squared_minus_1_dvd: (a^2 - 1) ∣ (a^2 - 1) := by apply Nat.dvd_refl
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd (a^2 - 1) (a^2 - 1)).mpr h_a_squared_minus_1_dvd

  -- Crucial relationship: a ≡ -1 (mod m)
  have h0: (a: ZMod m) = (-1: ZMod m) := by
    calc
      _ = (a + 1 - 1: ZMod m) := by ring
      _ = (-1: ZMod m) := by rw [h_a_plus_1]; ring

  -- Division algorithm relationship
  have h1: ∀ k, (a+1) * (q k) + r k = a^k := by
    intro k
    dsimp only [q, r]
    exact Nat.div_add_mod (a^k) (a+1)

  -- Key relationship between remainders and powers of -1
  have h2: ∀ k, (-1: ZMod (a + 1))^k = (r k: ℕ) := by
    intro k
    have h2_1: (a+1) * (q k) + (r k: ZMod (a + 1)) = (a^k: ZMod (a + 1)) := by
      norm_cast
      rw [h1 k]

    calc
      _ = (a : ZMod m)^k := by rw [h0]
      _ = (a^k : ℕ) := by simp
      _ = ((a+1) * (q k) + r k: ℕ) := by rw [h1]
      _ = r k := by simp

  -- Pattern of remainders: 1 for even k, a for odd k
  have h3: ∀ k, r k = if Even k then 1 else a := by
    intro k
    -- discuss two cases:
    -- 1. k is even
    -- 2. k is odd
    by_cases hk : Even k
    . -- Case 1: k is even
      simp [hk]
      calc
        _ = ((r k): ZMod (a + 1)).val := by simp [h_r_k k]
        _ = ((-1: ZMod (a + 1))^k).val := by simp [h2 k]
        _ = (1: ZMod (a + 1)).val := by simp [hk]
        _ = 1 % (a + 1) :=by exact rfl
        _ = 1 := Nat.mod_eq_of_lt (by omega)

    . -- Case 2: k is odd
      simp [hk]
      have h_odd_k: Odd k := Nat.not_even_iff_odd.mp hk
      calc
        _ = ((r k): ZMod (a + 1)).val := by simp [h_r_k k]
        _ = ((-1: ZMod (a + 1))^k).val := by simp [h2 k]
        _ = (-1: ZMod (a + 1)).val := by simp [h_odd_k]
        _ = (a: ZMod m).val := by simp [h0]
        _ = a % (a + 1) :=rfl
        _ = a := Nat.mod_eq_of_lt (by omega)

  -- Sum of remainders computation
  have h4: ∑ k ∈ Finset.Ico 1 2015, r k = 1007 * (a + 1) := by
    have h_even : ((Finset.Ico 1 2015).filter Even).card = 1007 := by native_decide
    have h_odd : ((Finset.Ico 1 2015).filter (fun k => ¬ Even k)).card = 1007 := by native_decide
    calc
      _ = ∑ k ∈ Finset.Ico 1 2015, r k := by simp

      _ = ∑ k ∈ Finset.Ico 1 2015, if Even k then 1 else a := by simp [h3]

      -- divide into two parts: even and odd
      _ = ∑ k ∈ (Finset.Ico 1 2015).filter Even, 1 + ∑ k ∈ (Finset.Ico 1 2015).filter (fun k => ¬ Even k), a := by rw [Finset.sum_ite]

      -- use card to compute the sum
      _ = ((Finset.Ico 1 2015).filter Even).card * 1 + ((Finset.Ico 1 2015).filter (fun k => ¬ Even k)).card * a := by simp
      _ = 1007 * 1 + 1007 * a := by rw [h_even, h_odd]
      _ = 1007 * (a + 1) := by ring

  -- Geometric sum application
  have h5: ∑ k ∈ Finset.Ico 1 2015, (a^k) = a * (a^2014 - 1) / (a - 1) := by
    have h_a_minus_1: (a^2015 - 1) - (a - 1) = a^2015 - a := by omega
    calc
      _ = ∑ k ∈ Finset.Ico 1 2015, (a^k) := by simp

      -- use geom_sum_2 to compute the sum
      _ = (a^2015 - 1)/(a - 1) - 1 := geom_sum_2 a 2015 (by omega) (by omega)
      _ = ((a^2015 - 1) - (a - 1))/(a - 1) := by
          rw [Nat.div_eq_sub_div h_pos h_le]
          norm_num
      _ = (a^2015 - a)/(a - 1) := by rw [h_a_minus_1]

      _ = a * (a^2014 - 1) / (a - 1) := by
        have h1: a^2015 = a * a^2014 := by ring
        have h2: a^2015 - a = a * (a^2014 - 1) := by
          rw [h1]
          rw [mul_tsub]
          ring_nf
        rw [h2]

  -- Key transformation of the sum
  have h6: (∑ k ∈ Finset.Ico 1 2015, q k) + 1007 = ∑ k ∈ Finset.range 1007, (a^(2*k + 1)) := by
    have h_dvd_a_minus_1: a^2 - 1 ∣ a^2014 - 1 := by
      rw [show a^2014 - 1 = (a^2)^1007 - 1^1007 by ring_nf]
      exact nat_sub_dvd_pow_sub_pow (a^2) 1 1007

    -- use h5 to compute the sum
    have h6_1: a * (a ^ 2014 - 1) / (a - 1) = ((∑ k ∈ Finset.Ico 1 2015, q k)  + 1007) * (a+1):= by
      calc
        _ = ∑ k ∈ Finset.Ico 1 2015, (a^k) := by rw [h5]
        _ = ∑ k ∈ Finset.Ico 1 2015, ((a+1) * (q k) + r k) := by simp [h1]
        _ = ∑ k ∈ Finset.Ico 1 2015, (a+1) * (q k) + ∑ k ∈ Finset.Ico 1 2015, r k := by rw [Finset.sum_add_distrib]
        _ = ∑ k ∈ Finset.Ico 1 2015, q k * (a+1) + ∑ k ∈ Finset.Ico 1 2015, r k := by simp[mul_comm]
        _ = (∑ k ∈ Finset.Ico 1 2015, q k) * (a+1) + ∑ k ∈ Finset.Ico 1 2015, r k := by rw [←Finset.sum_mul]
        _ = (∑ k ∈ Finset.Ico 1 2015, q k) * (a+1) + 1007 * (a+1) := by rw [h4]
        _ = ((∑ k ∈ Finset.Ico 1 2015, q k)  + 1007) * (a+1) := by ring

    -- use h6_1 to compute the sum
    have h_a_squred: (a + 1)*(a - 1) = a^2 - 1:= by exact (Nat.sq_sub_sq a 1).symm

    -- use h_a_squred to compute the sum
    have h6_2: (∑ k ∈ Finset.Ico 1 2015, q k)  + 1007 = ∑ k ∈ Finset.range 1007, (a^(2*k + 1)):= by
      calc
        _ = a * (a ^ 2014 - 1) / (a - 1) / (a + 1) := by simp [h6_1]
        _ = a * (a ^ 2014 - 1) / (a^2 - 1) := by
          rw [Nat.div_div_eq_div_mul]
          rw [show (a - 1) * (a + 1) = a^2 - 1 by rw [mul_comm, h_a_squred]]
        _ = a * ((a ^ 2014 - 1) / (a^2 - 1)) := by exact Nat.mul_div_assoc a h_dvd_a_minus_1
        _ = a * (((a ^ 2)^1007 - 1) / (a^2 - 1)) := by rw [←pow_mul]
        _ = a * (∑ k ∈ Finset.range 1007, (a^2)^k) := by
          rw [Nat.geomSum_eq (by nlinarith) 1007]
        _ = a * (∑ k ∈ Finset.range 1007, (a^(2*k))) := by simp only [←pow_mul]
        _ = (∑ k ∈ Finset.range 1007, (a^(2*k+1))) := by rw [Finset.mul_sum]; nth_rw 1 [show a=a^1 by ring];simp only[pow_add,mul_comm]

    exact h6_2

  set N := (a^2 - 1)

  -- Modular arithmetic simplification
  have h7: ∀ k, (a^(2*k + 1) : ZMod N) = a := by
    intro k
    have h7_1: (a^2: ZMod N) = 1 := by
      calc
        _ = (a^2 - 1 + 1: ZMod N) := by simp
        _ = 0 + 1 := by rw [h_a_squared_minus_1]
        _ = 1 := by simp

    calc
      _ = (a: ZMod N)* (a^2)^k := by ring
      _ = (a: ZMod N) * (1: ZMod N)^k := by rw [h7_1]
      _ = a := by ring

  -- Final steps combining all results
  have h8: ((∑ k ∈ Finset.range 1007, (a^(2*k + 1)) :ℕ): ZMod N) = 1007 * ↑a := by
    calc
      _ = ∑ k ∈ Finset.range 1007, (↑(a^(2*k + 1))) := Nat.cast_sum (Finset.range 1007) (fun k => a^(2*k + 1))
      _ = ∑ k ∈ Finset.range 1007, (a: ZMod N) := by
        apply Finset.sum_congr rfl
        intro x _
        simp [h7]
      _ = 1007 * ↑a := by simp [Finset.sum_const]

  -- Final conclusion
  have h9: ((∑ k ∈ Finset.Ico 1 2015, q k):ℕ) = ((1007 * (a - 1) : ℕ): ZMod N) := by

    -- use h8 to compute the sum
    have h9_1: ↑(∑ k ∈ Finset.Ico 1 2015, q k) + (1007: ZMod N) = 1007 * (a : ZMod N):= by
      calc
        _ = (((∑ k ∈ Finset.Ico 1 2015, q k) + 1007:ℕ): ZMod N) := by
          push_cast
          rfl
        _ = ↑(∑ k ∈ Finset.range 1007, (a^(2*k + 1))) := by rw [h6]
        _ = 1007 * ↑a := by
          rw [h8]

    -- use h9_1 to compute the sum
    have h9_2: ↑(∑ k ∈ Finset.Ico 1 2015, q k) = ((1007 * (a - 1) : ℕ): ZMod N):= by
      calc
        _ = ↑(∑ k ∈ Finset.Ico 1 2015, q k) + (1007: ZMod N) - (1007: ZMod N) := by ring
        _ = 1007 * (a : ZMod N) - (1007: ZMod N) := by rw [h9_1]
        _ = 1007 * (a - 1: ZMod N) := by ring
        _ = ((1007 * (a - 1) : ℕ): ZMod N) := by
          push_cast
          rw [Nat.cast_sub, Nat.cast_one]
          omega
    exact h9_2
  exact h9
