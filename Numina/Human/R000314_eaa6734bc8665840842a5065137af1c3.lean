import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Determine all integers  $a$  and  $b$  such that
\[(19a + b)^{18} + (a + b)^{18} + (a + 19b)^{18}\]
is a perfect square.-/
theorem number_theory_8893 (a b : ℤ) : IsSquare ((19 * a + b)^18 + (a + b)^18 + (a + 19 * b)^18) ↔
    a = 0 ∧ b = 0 := by
  constructor
  swap
  -- Verify that a=0,b=0 is soution.
  . rintro ⟨rfl, rfl⟩
    norm_num
  intro hab
  by_contra hab_ne_zero
  rw [not_and_or] at hab_ne_zero
  wlog habcoprime : IsCoprime a b
  -- We just need to use  $mod$   $19$ .
  -- If  $(a,b)=k$ , we can put  $a=ka_1$ ,  $b=kb_1$ .
  -- So we observe if  $(a,b)$  is a solution, so  $(a_1,b_1)$  is a solution too.
  -- So we just need to take  $(a,b)=1$ .
  . rcases hab with ⟨k, hk⟩
    obtain ⟨u, hu⟩ : ↑(a.gcd b) ∣ a := Int.gcd_dvd_left
    obtain ⟨v, hv⟩ : ↑(a.gcd b) ∣ b := Int.gcd_dvd_right
    rw [← Int.gcd_eq_one_iff_coprime] at habcoprime
    have hgcd_pos : 0 < a.gcd b := hab_ne_zero.elim
      (Int.gcd_pos_of_ne_zero_left _ ·)
      (Int.gcd_pos_of_ne_zero_right _ ·)
    have hdiv_gcd_coprime := Nat.coprime_div_gcd_div_gcd hgcd_pos
    refine this (a / a.gcd b) (b / a.gcd b) ?_ ?_ ?_
    . set d := a.gcd b with hd
      rw [hu, hv, ← mul_assoc, mul_comm 19, mul_assoc, ← mul_add, ← mul_add,
        ← mul_assoc, mul_comm 19 (d : ℤ), mul_assoc, ← mul_add, mul_pow, mul_pow, mul_pow,
        ← mul_add, ← mul_add] at hk
      have hd_dvd_k : (d : ℤ) ^ 18 ∣ k * k := Exists.intro _ hk.symm
      rw [← pow_two, show (d : ℤ) ^ 18 = (d ^ 9)^2 by ring,
        Int.pow_dvd_pow_iff (by norm_num)] at hd_dvd_k
      rcases hd_dvd_k with ⟨z, hz⟩
      use z
      have : (d : ℤ) ^ 18 ≠ 0 := by
        norm_cast
        change _ ≠ _
        rw [← Nat.pos_iff_ne_zero]
        exact Nat.pow_pos hgcd_pos
      rw [← Int.mul_eq_mul_left_iff this]
      convert hk using 1
      . have hadu : a / (d : ℤ) = u := by
          rw [hu, mul_comm, Int.mul_ediv_cancel]
          exact_mod_cast hgcd_pos.ne'
        have hbdv : b / (d : ℤ) = v := by
          rw [hv, mul_comm, Int.mul_ediv_cancel]
          exact_mod_cast hgcd_pos.ne'
        rw [hadu, hbdv]
      . rw [hz]; ring
    . refine hab_ne_zero.elim (fun h => ?_) (fun h => ?_)
      . left
        intro haediv
        apply_fun (· * (a.gcd b : ℤ)) at haediv
        rw [Int.ediv_mul_cancel Int.gcd_dvd_left, zero_mul] at haediv
        contradiction
      . right
        intro hbediv
        apply_fun (· * (a.gcd b : ℤ)) at hbediv
        rw [Int.ediv_mul_cancel Int.gcd_dvd_right, zero_mul] at hbediv
        contradiction
    . rw [Int.coprime_iff_nat_coprime]
      convert hdiv_gcd_coprime
      . rw [Int.natAbs_ediv _ _ Int.gcd_dvd_left, Int.gcd, Int.natAbs_cast]
      . rw [Int.natAbs_ediv _ _ Int.gcd_dvd_right, Int.gcd, Int.natAbs_cast]
  have hprime19 : Nat.Prime 19 := by norm_num
  have coprime19_of_not_dvd {n : ℤ} (hdvd : ¬19 ∣ n) : IsCoprime n (19 : ℕ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd, ← Nat.coprime_iff_gcd_eq_one]
    norm_cast
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hprime19]
    zify
    rwa [dvd_abs]
  have self_mod19 : 19 ≡ 0 [ZMOD 19] := rfl
  have mul19_mod19 (n : ℤ) : 19 * n ≡ 0 [ZMOD 19] := by
    have := Int.ModEq.mul_right n self_mod19
    rwa [zero_mul] at this
  have h1 := (mul19_mod19 a).add (Int.ModEq.refl b)
  have h2 := @Int.ModEq.refl 19 (a + b)
  have h3 := (Int.ModEq.refl a).add (mul19_mod19 b)
  have H := ((h1.pow 18).add (h2.pow 18)).add (h3.pow 18)
  rw [zero_add, add_zero] at H
  clear h1 h2 h3
  have hnot19dvd : ¬(19 ∣ a ∧ 19 ∣ b) := by
    rintro ⟨ha, hb⟩
    rw [Int.isCoprime_iff_gcd_eq_one] at habcoprime
    have := Int.dvd_gcd ha hb
    rw [habcoprime] at this
    norm_num at this
  rcases hab with ⟨k, hk⟩
  -- We can deduce b ≠ 0 [mod 19] from a = 0 [mod 19].
  by_cases h19dvda : 19 ∣ a
  . have : ¬ 19 ∣ b := fun h => hnot19dvd ⟨h19dvda, h⟩
    have := coprime19_of_not_dvd this
    have hbpow_eq_one := Int.ModEq.pow_card_sub_one_eq_one hprime19 this
    replace hbpow_eq_one := hbpow_eq_one.mul_left 2
    rw [show 19 - 1 = 18 by norm_num, mul_one] at hbpow_eq_one
    have amod19 : a ≡ 0 [ZMOD 19] := by rwa [Int.modEq_zero_iff_dvd]
    have add_abmod19 := amod19.add (Int.ModEq.refl b)
    have := ((Int.ModEq.refl b).pow 18).add (add_abmod19.pow 18)
    have := this.add (amod19.pow 18)
    rw [zero_add, zero_pow (by norm_num), add_zero, ← two_mul] at this
    have := Int.ModEq.trans H this
    have H := Int.ModEq.trans this hbpow_eq_one
    rw [hk, Int.ModEq, Int.mul_emod] at H
    -- Further, we have x^2 = 2 [mod 19] which is impossible.
    have : 0 ≤ k % 19 := Int.emod_nonneg _ (by norm_num)
    have : k % 19 < 19 := Int.emod_lt_of_pos _ (by norm_num)
    interval_cases k % 19
    all_goals norm_num at H
  -- We just need to check the case  $a\neq0$ ,  $b=0$  and  $a=0$ ,
  -- $b\neq0$  (which are analogous).
  -- In the first case we need  $x^2=2\pmod{19}$, but this is not true.
  by_cases h19dvdb : 19 ∣ b
  . have := coprime19_of_not_dvd h19dvda
    have hapow_eq_one := Int.ModEq.pow_card_sub_one_eq_one hprime19 this
    replace hapow_eq_one := hapow_eq_one.mul_left 2
    norm_num at hapow_eq_one
    have bmod19 : b ≡ 0 [ZMOD 19] := by rwa [Int.modEq_zero_iff_dvd]
    have add_abmod19 := (Int.ModEq.refl a).add bmod19
    have := (bmod19.pow 18).add (add_abmod19.pow 18)
    have := this.add ((Int.ModEq.refl a).pow 18)
    rw [zero_pow (by norm_num), zero_add, add_zero, ← two_mul] at this
    have := Int.ModEq.trans H this
    have H := Int.ModEq.trans this hapow_eq_one
    rw [hk, Int.ModEq, Int.mul_emod] at H
    -- but there is no  $x$  integer such that  $x^2=2$   $(mod$   $19)$ .
    have : 0 ≤ k % 19 := Int.emod_nonneg _ (by norm_num)
    have : k % 19 < 19 := Int.emod_lt_of_pos _ (by norm_num)
    interval_cases k % 19
    all_goals norm_num at H
  -- If a+b = 0 [mod 19], then x^2 = 2 [mod 19] which is impossible.
  by_cases h19dvdab : 19 ∣ a + b
  . have h1 := Int.ModEq.pow_card_sub_one_eq_one hprime19 (coprime19_of_not_dvd h19dvda)
    have h2 := Int.ModEq.pow_card_sub_one_eq_one hprime19 (coprime19_of_not_dvd h19dvdb)
    have h3 : a + b ≡ 0 [ZMOD 19] := by rwa [Int.modEq_zero_iff_dvd]
    have := (h2.add (h3.pow 18)).add h1
    norm_num at this
    have H := Int.ModEq.trans H this
    rw [hk, Int.ModEq, Int.mul_emod] at H
    have : 0 ≤ k % 19 := Int.emod_nonneg _ (by norm_num)
    have : k % 19 < 19 := Int.emod_lt_of_pos _ (by norm_num)
    interval_cases k % 19
    all_goals norm_num at H
  -- If a,b,a+b are coprime to 19.
  -- By the Little Fermat Theorem, we can see $(19a+b)^{18}+(a+b)^{18}+(a+19b)^{18}=1+1+1=3$   $(mod$   $19)$ ,
  have h1 := Int.ModEq.pow_card_sub_one_eq_one hprime19 (coprime19_of_not_dvd h19dvda)
  have h2 := Int.ModEq.pow_card_sub_one_eq_one hprime19 (coprime19_of_not_dvd h19dvdb)
  have h3 := Int.ModEq.pow_card_sub_one_eq_one hprime19 (coprime19_of_not_dvd h19dvdab)
  have H1 := Int.ModEq.add h2 <| Int.ModEq.add h3 h1
  rw [show 19 - 1 = 18 by norm_num, ← add_assoc] at H1
  clear h1 h2 h3
  replace H1 := Int.ModEq.trans H H1
  rw [hk, Int.ModEq, Int.mul_emod] at H1
  -- but there is no  $x$  integer such that  $x^2=3$   $(mod$   $19)$ .
  have : 0 ≤ k % 19 := Int.emod_nonneg _ (by norm_num)
  have : k % 19 < 19 := Int.emod_lt_of_pos _ (by norm_num)
  interval_cases k % 19
  all_goals norm_num at H1
