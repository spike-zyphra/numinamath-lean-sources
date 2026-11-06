import Mathlib

/- Find all triplets of positive integers $(p, n, m)$ such that $p$ is prime and $p^{n}+144=m^{2}$ -/
theorem number_theory_116465 (p n m : ℕ) (hp : p.Prime)
    (hn : 0 < n) (hm : 0 < m) (h : p ^ n + 144 = m ^ 2) :
    (p = 5 ∧ n = 2 ∧ m = 13) ∨ (p = 2 ∧ n = 8 ∧ m = 20) ∨
    (p = 3 ∧ n = 4 ∧ m = 15) := by
  have hm : 12 ^ 2 ≤ m ^ 2 := by omega
  rw [Nat.pow_le_pow_iff_left two_ne_zero] at hm

  -- To begin, we factor p^n + 144 = m^2 to get p^n = (m - 12)(m + 12)
  have h : p ^ n = (m - 12) * (m + 12) := by
    rw [mul_comm, ← mul_self_tsub_mul_self, ← sq, show 12 * 12 = 144 by omega, ← h,
      add_tsub_cancel_right]
  -- As p^n is a prime power, we obtain m - 12 = p^a and m + 12 = p^b for some a, b adding to n
  obtain ⟨a, ha, ha'⟩ : ∃ a ≤ n, m - 12 = p ^ a := by
    exact (Nat.dvd_prime_pow hp).mp <| h.symm ▸ Nat.dvd_mul_right (m - 12) (m + 12)
  obtain ⟨b, hb, hb'⟩ : ∃ b ≤ n, m + 12 = p ^ b := by
    exact (Nat.dvd_prime_pow hp).mp <| h.symm ▸ Nat.dvd_mul_left (m + 12) (m - 12)
  rw [ha', hb', ← pow_add] at h
  have hn' := Nat.pow_right_injective hp.two_le h

  -- Now, we consider two cases: a = 0 or a > 0
  by_cases ha : 0 < a
  · -- If a > 0, notice that p^b - p^a = 24, so p^a ∣ 24.
    have : m - 12 ≤ m + 12 := by omega
    have : a ≤ b := by rwa [ha', hb', Nat.pow_le_pow_iff_right hp.two_le] at this
    have : p ∣ p ^ b - p ^ a := by
      apply Nat.dvd_sub
      · omega
      · exact ⟨p ^ (b - 1), by nth_rw 2 [← pow_one p]; rw [← pow_add]; congr 1; omega⟩
      · exact ⟨p ^ (a - 1), by nth_rw 2 [← pow_one p]; rw [← pow_add]; congr 1; omega⟩
    have h : p ^ b - p ^ a = 24 := by
      rw [← hb', ← ha']
      omega
    have : p ∣ 24 := by
      convert this
      exact h.symm
    -- This implies p = 2 or p = 3
    have : p ∈ Nat.primeFactors 24 := by
      rw [Nat.mem_primeFactors]
      tauto
    have h : Nat.primeFactors 24 = {2, 3} := by
      native_decide
    have : p = 2 ∨ p = 3 := by
      simpa [h] using this
    rcases this with rfl | rfl
    · -- If p = 2, then a ≤ 3, so we check each case and see that (a, b) = (3, 5) is the only
      -- solution.
      have : 24 ≤ 2 ^ b := by rw [← h]; omega
      have : 2 ^ 4 < 2 ^ b := by omega
      have : 5 ≤ b := (Nat.pow_lt_pow_iff_right one_lt_two).mp this
      have h' : (2 ^ (b - a) - 1) * 2 ^ a = 24 := by
        rw [← h, Nat.sub_mul, one_mul, ← Nat.pow_add, tsub_add_cancel_of_le ‹_›]
      have : 2 ^ a ∣ 24 := by
        rw [← h']
        exact Nat.dvd_mul_left _ _
      have ha_le : a ≤ 3 := by
        by_contra! ha : 4 ≤ a
        have : 2 ^ 4 ∣ 24 := (Nat.pow_dvd_pow _ ha).trans this
        norm_num at this
      interval_cases a
      · have : m = 14 := by omega
        have : 2 ^ b = 26 := by omega
        have : 2 ^ 5 ≤ 2 ^ b := Nat.pow_le_pow_right zero_lt_two ‹_›
        omega
      · have : 2 ^ (b - 2) = 7 := by omega
        have : 2 ^ 3 ∣ 7 := by
          rw [← this]
          apply Nat.pow_dvd_pow
          omega
        norm_num at this
      · have : 2 ^ (b - 3) = 2 ^ 2 := by omega
        have : b - 3 = 2 := Nat.pow_right_injective (le_refl _) this
        omega
    · -- If p = 3, then a ≤ 1, from which (a, b) = (1, 3).
      have : 24 ≤ 3 ^ b := by rw [← h]; omega
      have : 3 ^ 2 < 3 ^ b := by omega
      have : 3 ≤ b := (Nat.pow_lt_pow_iff_right (by decide)).mp this
      have h' : (3 ^ (b - a) - 1) * 3 ^ a = 24 := by
        rw [← h, Nat.sub_mul, one_mul, ← Nat.pow_add, tsub_add_cancel_of_le ‹_›]
      have : 3 ^ a ∣ 24 := by
        rw [← h']
        exact Nat.dvd_mul_left _ _
      have ha_le : a ≤ 1 := by
        by_contra! ha : 2 ≤ a
        have : 3 ^ 2 ∣ 24 := (Nat.pow_dvd_pow _ ha).trans this
        norm_num at this
      have : a = 1 := by omega
      subst this
      have : 3 ^ (b - 1) = 3 ^ 2 := by omega
      have := Nat.pow_right_injective (by decide) this
      omega

  · -- If a = 0, then p^b = 25, so (p, b) = (5, 2)
    obtain ⟨rfl⟩ : a = 0 := by omega
    simp at ha'
    obtain ⟨rfl⟩ : m = 13 := by omega
    rw [show 13 + 12 = 5 ^ 2 by norm_num] at hb'
    rw [zero_add] at hn'
    subst hn'
    have : 5 ^ (1 + 1) = p ^ ((n - 1) + 1) := by
      convert hb'
      omega
    have := Nat.Prime.pow_inj (by norm_num) hp this
    omega