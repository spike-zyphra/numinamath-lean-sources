import Mathlib


namespace number_theory_609540

lemma fermatLittle {a p : ℕ} (hp : Nat.Prime p) (ha : a.Coprime p) : a^(p-1) ≡ 1 [MOD p] := by
  have : IsCoprime (a : ℤ) (p : ℤ) := by simp [Int.coprime_iff_nat_coprime]
                                         exact ha

  let fermat := @Int.ModEq.pow_card_sub_one_eq_one p hp a this
  rw [← Int.natCast_modEq_iff]
  ring_nf
  have : ∃ m : ℕ, p = m + 1 := by refine Nat.exists_eq_add_of_le' ?h; exact Nat.Prime.one_le hp
  obtain ⟨ m, hm ⟩ := this
  rw [hm]
  rw [hm] at fermat
  simp at *
  exact fermat

lemma fermatMin {a p : ℕ} (hp : Nat.Prime p) (ha : a.Coprime p) :
  ∃ d : ℕ, d ≥ 1 ∧ d ≤ p - 1 ∧ a^d ≡ 1 [MOD p] ∧
    (∀ n : ℕ, a^n ≡ 1 [MOD p] → d ∣ n) := by

  let s := (Finset.Icc 1 (p - 1)).filter (fun k ↦ a^k ≡ 1 [MOD p])

  have : s.Nonempty := by
    have : p - 1 ∈ s := by simp [s]
                           constructor
                           . have : 1 = 2 - 1 := by norm_num
                             nth_rewrite 1 [this]
                             rw [Nat.sub_le_sub_iff_right]
                             exact Nat.Prime.two_le hp
                             exact Nat.Prime.one_le hp
                           . apply fermatLittle hp ha

    use p-1

  obtain ⟨ d, hd ⟩ := Finset.min_of_nonempty this
  use d
  have : d ∈ s := by apply Finset.mem_of_min; exact hd

  rw [Finset.mem_filter] at this
  obtain ⟨ hl, hr ⟩ := this
  simp [Finset.mem_Ioc] at hl
  have ⟨ hll, hlr ⟩ := hl
  refine And.intro hll ?_
  refine And.intro hlr ?_
  refine And.intro hr ?_
  intro n hmodn
  rw [← Nat.mod_add_div n d, pow_add, pow_mul] at hmodn
  have : a ^ (n % d) * (a ^ d) ^ (n / d) ≡ a ^ (n % d) * 1 [MOD p] := by
    apply Nat.ModEq.mul_left
    apply Nat.ModEq.pow (n / d) at hr
    simp at hr
    exact hr
  by_cases hrem : n % d ≥ 1
  . have hnltmin : n % d < d := by apply Nat.mod_lt; exact hll
    have hrs : n % d ∈ s := by
      simp [s]
      constructor
      . refine And.intro hrem ?_
        linarith
      . obtain ggg := Nat.ModEq.trans (Nat.ModEq.symm this) hmodn
        simp at ggg
        exact ggg
    obtain hmin := Finset.min_le_of_eq hrs hd
    linarith
  . simp at hrem
    apply Nat.dvd_of_mod_eq_zero at hrem
    assumption

end number_theory_609540

open number_theory_609540

theorem number_theory_609540 (s : Finset ℕ) :
  s = (Finset.Icc 2 2016).filter (fun n : ℕ ↦ ∀ p ∈ [2,3,5,7], n^n ≡ 1 [MOD p]) → s.card = 9 := by
  intro hs
  rw [hs]
  native_decide