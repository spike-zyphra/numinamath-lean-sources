import Mathlib

theorem number_theory_639739 (X : ℕ) (hX : X > 0) (N1 N2 n : ℕ)
  (hN1 : N1 = 101 + X * 625) (hN2 : N2 = 101 + (X + 5) * 625)
  (hN : N1 % n = N2 % n) (hN1' : 100 ≤ n ∧ n ≤ 999) :
  N1 % n = 101 := by 
  obtain ⟨hn1, hn2⟩ := hN1'
  zify at hN hN1 hN2 ⊢ -- Convert natural numbers to integers for modular calculations.
  have ndvd : (n : ℤ)∣ (N1 - N2) := by 
    exact Int.ModEq.dvd (id (Eq.symm hN))
  rw [hN1, hN2] at ndvd
  ring_nf at ndvd
  simp at ndvd
  norm_cast at ndvd
  rw [show 3125 = 5 ^ 5 by norm_num] at ndvd
  have prime5 : Nat.Prime 5 := by norm_num
  obtain ⟨k, hkle, hneq⟩ := (Nat.dvd_prime_pow prime5).mp ndvd
  have neq_or : n = 125 ∨ n = 625 := by 
    -- since k ≤ 5, then discuss by cases k = 0 to 5, and use the assumption that n ≥ 100, n ≤ 999, we can draw these two conclusions.
    interval_cases k <;> simp_all [← pow_succ]
  obtain neq | neq := neq_or
  · -- case n = 125
    rw [neq, hN1]
    omega
  · -- case n = 625
    rw [neq, hN1]
    omega