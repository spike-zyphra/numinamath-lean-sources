import Mathlib

/-
9. [7] The largest prime factor of 101101101101 is a four-digit number $N$. Compute $N$.
-/

theorem number_theory_183299 (n p : ℕ) (hn: n = 101101101101)(hp: Nat.Prime p)(h:IsGreatest {p | p.Prime ∧ p ∣ n} p)(h2: 1000 ≤ p ∧ p ≤ 9999) : p = 9901 := by
  
  --If prime p divides n, we prove that p ≤ 9901 by checking the factors of n.
  have : p ≤ 9901 := by 
    have pdn: p ∣ n := by 
      unfold IsGreatest at h
      exact h.1.2
    have : n = 7*11*13*101^2 * 9901 := by simp [hn]
    rw [this] at pdn
    have p7 : Nat.Prime 7 := by norm_num
    have p11: Nat.Prime 11:= by norm_num
    have p13: Nat.Prime 13:= by norm_num
    have p101: Nat.Prime 101 := by norm_num
    have p9901: Nat.Prime 9901 := by norm_num

    have : p ∣ 7*11*13*101^2 ∨ p ∣ 9901 := by exact (Nat.Prime.dvd_mul hp).mp pdn
    rcases this with (pdv|pdv)
    -- if p divide 7 * 11 * 13 * 101 ^ 2, then p < 9901
    by_cases pd101 : p ∣ 101
    have : p ≤ 101 := by apply Nat.le_of_dvd; linarith; exact pd101
    linarith
    have : p.Coprime 101 := by exact (Nat.Prime.coprime_iff_not_dvd hp).mpr pd101
    have : p.Coprime (101^2) := by exact Nat.Coprime.pow_right 2 this
    have : p ∣ 7*11*13 := by exact (Nat.Coprime.dvd_mul_left this).mp pdv
    have : p ≤ 7*11*13 := by apply Nat.le_of_dvd; linarith; exact this
    linarith
    
    apply Nat.le_of_dvd
    linarith
    exact pdv

  --9901 is a prime factor of n, so 9901 ≤ p.
  have : 9901 ≤ p := by 
    have : 9901 ∈ {p | p.Prime ∧ p ∣ n} := by
      simp [hn]
      norm_num
    exact h.2 this
  linarith