import Mathlib

/-A positive integer k is called powerful if there are distinct positive integers p,q,r,s,t such that
p^2, q^3, r^5, s^7, t^11 all divide k. Find the smallest powerful integer.-/

theorem Number_Theory_609762: IsLeast {k: ℕ | (1 ≤ k) ∧ (∃ p q r s t: ℕ,  (p ^ 2 ∣ k) ∧ (q ^ 3 ∣ k) ∧ (r ^ 5 ∣ k) ∧ (s ^ 7 ∣ k) ∧ (t ^ 11 ∣ k)
∧ (p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ p ≠ t ∧ q ≠ r ∧ q ≠ s ∧ q ≠ t ∧ r ≠ s ∧ r ≠ t ∧ s ≠ t) ∧ (1 ≤ p) ∧ (1 ≤ q) ∧ (1 ≤ q) ∧(1 ≤ r) ∧(1 ≤ s) ∧ (1 ≤ t))} 1024 := by
  constructor
  . simp
    use 16
    constructor
    omega
    use 8
    constructor
    omega
    use 4
    constructor
    omega
    use 2
    constructor
    omega
    use 1
    constructor
    omega
    omega
  . simp
    intro x
    intro hx
    simp at hx
    obtain ⟨hx,hp⟩:= hx
    rcases hp with ⟨p,h⟩
    rcases h with ⟨hp,h⟩
    rcases h with ⟨q,h⟩
    rcases h with ⟨hq,h⟩
    rcases h with ⟨r,h⟩
    rcases h with ⟨hr,h⟩
    rcases h with ⟨s,h⟩
    rcases h with ⟨hs,h⟩
    rcases h with ⟨t,h⟩
    rcases h with ⟨ht,h⟩
    rcases h with ⟨h1,h⟩
    rcases h with ⟨h2,h⟩
    rcases h with ⟨h3,h⟩
    rcases h with ⟨h4,h⟩
    rcases h with ⟨h5,h⟩
    rcases h1 with ⟨k1,k2,k3,k4,k5,k6,k7,k8,k9,k10⟩
    by_contra! H
    have w1: t ≤ 1 := by
      by_contra! w1
      replace w1: 2 ≤ t := by omega
      apply Nat.le_of_dvd at ht
      replace ht: 2 ^ 11 ≤ 1024 := by
        calc
          2 ^ 11 ≤ t ^ 11 := by apply Nat.pow_le_pow_of_le_left; omega
                _≤ 1024 := by omega
      simp at ht
      omega
    replace w1: t = 1 := by omega
    by_cases hs1: s ≥ 3
    . apply Nat.le_of_dvd at hs
      replace hs: 3 ^ 7 ≤ 1024 := by
        calc
          3 ^ 7 ≤ s ^ 7 := by apply Nat.pow_le_pow_of_le_left; omega
                _≤ 1024 := by omega
      simp at hs
      omega
    . rw [w1] at k10
      replace hs1: s = 2 := by omega
      by_cases hr1: r ≥ 4
      . apply Nat.le_of_dvd at hr
        replace hr: 4 ^ 5 ≤ x := by
          calc
            4 ^ 5 ≤ r ^ 5 := by apply Nat.pow_le_pow_of_le_left; omega
                  _≤ x := by omega
        simp at hr
        omega
        omega
      . rw [w1] at k9
        rw [hs1] at k8
        replace hr1: r = 3 := by omega
        rw [hr1] at hr
        rw [hs1] at hs
        have dvd: 3 ^ 5 * 2 ^ 7 ∣x := by
          apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
          norm_num
          exact hr
          exact hs
        simp at dvd
        apply Nat.le_of_dvd at dvd
        omega
        omega