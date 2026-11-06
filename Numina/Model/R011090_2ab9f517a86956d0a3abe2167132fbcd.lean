import Mathlib

theorem algebra_12792: IsLeast {n: ℕ | 0 < n ∧ ∃ p q r s, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ Nat.Prime s ∧
  p < q ∧ q < r ∧ r < s ∧ p ∣ n ∧  q ∣ n ∧  r ∣ n ∧ s ∣ n} 210 := by
  constructor
  · -- Show 210 is in the set.
    constructor
    · norm_num
    · use 2, 3, 5, 7
      all_goals norm_num
  · -- Show 210 is the least in the set.
    intro n hn
    rcases hn with ⟨hn_pos, p, q, r, s, hp, hq, hr, hs, h1, h2, h3, h4, h5, h6, h7⟩
    by_contra h
    push_neg at h
    have h8 : p ≥ 2 := by
      by_contra h
      push_neg at h
      interval_cases p <;> norm_num at hp
    have h9 : q ≥ 3 := by
      by_contra h
      push_neg at h
      interval_cases q <;> norm_num at hq
      all_goals omega
    have h10 : r ≥ 5 := by
      by_contra h
      push_neg at h
      interval_cases r <;> norm_num at hr
      all_goals omega
    have h11 : s ≥ 7 := by
      by_contra h
      push_neg at h
      interval_cases s <;> norm_num at hs
      all_goals omega
    have h12 : p ∣ n := h4
    have h13 : q ∣ n := h5
    have h14 : r ∣ n := h6
    have h15 : s ∣ n := h7
    have h21 : Nat.Coprime p q := by
      have h22 : p < q := h1
      have h23 : Nat.Prime p := hp
      have h24 : Nat.Prime q := hq
      have h25 : p ≠ q := by omega
      have h26 : Nat.Prime q := hq
      have h27 : Nat.Coprime p q := by
        apply (Nat.coprime_primes h23 h26).mpr
        omega
      exact h27
    have h23 : Nat.Coprime p r := by
      have h23 : p < r := by linarith [h1, h2]
      have h24 : Nat.Prime p := hp
      have h25 : Nat.Prime r := hr
      have h26 : p ≠ r := by
        omega
      have h27 : Nat.Coprime p r := by
        apply (Nat.coprime_primes h24 h25).mpr
        omega
      exact h27
    have h24 : Nat.Coprime p s := by
      have h27 : p < s := by linarith [h1, h2, h3]
      have h28 : Nat.Prime p := hp
      have h29 : Nat.Prime s := hs
      have h30 : p ≠ s := by
        omega
      have h31 : Nat.Coprime p s := by
        apply (Nat.coprime_primes h28 h29).mpr
        omega
      exact h31
    have h25 : Nat.Coprime q r := by
      have h28 : q < r := h2
      have h29 : Nat.Prime q := hq
      have h30 : Nat.Prime r := hr
      have h31 : q ≠ r := by
        omega
      have h32 : Nat.Coprime q r := by
        apply (Nat.coprime_primes h29 h30).mpr
        omega
      exact h32
    have h26 : Nat.Coprime q s := by
      have h29 : q < s := by linarith [h2, h3]
      have h30 : Nat.Prime q := hq
      have h31 : Nat.Prime s := hs
      have h32 : q ≠ s := by
        omega
      have h33 : Nat.Coprime q s := by
        apply (Nat.coprime_primes h30 h31).mpr
        omega
      exact h33
    have h27 : Nat.Coprime r s := by
      have h30 : r < s := h3
      have h31 : Nat.Prime r := hr
      have h32 : Nat.Prime s := hs
      have h33 : r ≠ s := by
        omega
      have h34 : Nat.Coprime r s := by
        apply (Nat.coprime_primes h31 h32).mpr
        omega
      exact h34
    have h18 : p * q ∣ n := by
      have h17 : p ∣ n := h4
      have h18 : q ∣ n := h5
      have h151 : Nat.Coprime p q := h21
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h151 h17 h18
    have h19 : (p * q) * r ∣ n := by
      have h17 : (p * q) ∣ n := h18
      have h18 : r ∣ n := h6
      have h151 : Nat.Coprime (p * q) r := by
        have h39 : Nat.Coprime p r := h23
        have h40 : Nat.Coprime q r := h25
        exact Nat.Coprime.mul h39 h40
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h151 h17 h18
    have h20 : ((p * q) * r) * s ∣ n := by
      have h17 : (p * q) * r ∣ n := h19
      have h18 : s ∣ n := h7
      have h151 : Nat.Coprime ((p * q) * r) s := by
        have h39 : Nat.Coprime (p * q) s := by
          have h41 : Nat.Coprime p s := h24
          have h42 : Nat.Coprime q s := h26
          exact Nat.Coprime.mul h41 h42
        have h40 : Nat.Coprime r s := h27
        exact Nat.Coprime.mul h39 h40
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h151 h17 h18
    have h28 : (p * q * r * s) ∣ n := by
      ring_nf at h20 ⊢
      exact h20
    have h29 : p * q * r * s > 0 := by
      have h29 : p ≥ 2 := h8
      have h30 : q ≥ 3 := h9
      have h31 : r ≥ 5 := h10
      have h32 : s ≥ 7 := h11
      have h24 : p * q * r * s > 0 := by
        have h214 : p > 0 := by linarith
        have h215 : q > 0 := by linarith
        have h216 : r > 0 := by linarith
        have h217 : s > 0 := by linarith
        positivity
      linarith
    have h30 : p * q * r * s ≤ n := by
      apply Nat.le_of_dvd (by linarith) h28
    have h31 : p * q * r * s ≤ 209 := by
      linarith [show n < 210 from h, h30]
    have h32 : p * q * r * s ≥ 210 := by
      have h33 : p ≥ 2 := h8
      have h34 : q ≥ 3 := h9
      have h35 : r ≥ 5 := h10
      have h36 : s ≥ 7 := h11
      have h37 : p * q * r * s ≥ 2 * 3 * 5 * 7 := by
        have hp2 : p ≥ 2 := h8
        have hq3 : q ≥ 3 := h9
        have hr5 : r ≥ 5 := h10
        have hs7 : s ≥ 7 := h11
        have h151 : p * q ≥ 2 * 3 := by
          nlinarith
        have h152 : r * s ≥ 5 * 7 := by
          nlinarith
        have h153 : (p * q * r * s) ≥ (2 * 3 * 5 * 7) := by
          have h191 : p * q * r * s = (p * q) * (r * s) := by ring
          rw [h191]
          have h192 : (2 * 3 * 5 * 7) = (2 * 3) * (5 * 7) := by ring
          rw [h192  ]
          nlinarith [show p * q ≥ 2 * 3 by nlinarith, show r * s ≥ 5 * 7 by nlinarith]
        linarith
      nlinarith
    omega