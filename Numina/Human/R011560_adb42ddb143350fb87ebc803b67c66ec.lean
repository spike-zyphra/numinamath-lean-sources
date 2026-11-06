import Mathlib

def x: ℕ → ℕ
| 0 => 2
| n + 1 => 5 + x n ^ 2

/-Let x0,x1,x2,...be the sequence defined by
x0 =2 and xn+1=5+xn^2 for every n≥0. Prove that this sequence does not contain any prime numbers other than 2.-/

theorem number_theory_134583: ∀ n, ¬ (Nat.Prime (x n) ∧ x n ≠ 2) := by

  -- we first show for 1 ≤ n, 3 < x n by induction
  have l: ∀ n, 1 ≤ n → 3 < x n := by
    intro n hn
    induction' n with n ih
    .
      linarith
    .
      by_cases s: n = 0
      .
        simp [s, x]
      .
        replace s: 1 ≤ n := by omega
        simp [s] at ih
        rw [x]
        nlinarith

  -- we show that for even n, x n is even
  have e: ∀ k, 2 ∣ (x (2 * k)) := by
    intro k
    induction' k with k ih
    .
      simp [x]
    .
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by rfl]
      rw [x]
      rw [x]
      apply exists_eq_mul_right_of_dvd at ih
      obtain ⟨m, hm⟩ := ih
      rw [hm]
      ring_nf
      rw [show 30 + m ^ 2 * 40 + m ^ 4 * 16 = 2 * (15 + m ^ 2 * 20 + m ^ 4 * 8) by ring]
      simp

  -- we show that for odd n, 3 ∣ x n
  have d: ∀ k, 3 ∣ (x (2 * k + 1)) := by
    intro k
    induction' k with k ih
    .
      simp [x]
      norm_num
    .
      rw [x]
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by rfl]
      rw [x]
      apply exists_eq_mul_right_of_dvd at ih
      obtain ⟨m, hm⟩ := ih
      rw [hm]
      ring_nf
      rw [show 30 + m ^ 2 * 90  + m ^ 4 * 81 = 3 * (10 + m ^ 2 * 30 + m ^ 4 * 27) by ring]
      simp

  intro n hn
  by_cases r: n = 0

  -- case n = 0
  .
    simp [r, x] at hn

  -- case 0 < n
  by_cases o: 2 ∣ n

  -- case n is even
  .
    apply exists_eq_mul_right_of_dvd at o
    obtain ⟨k, hk⟩ := o
    specialize e k
    rw [← hk] at e
    rcases hn with ⟨h1, h2⟩
    rw [Nat.prime_dvd_prime_iff_eq] at e
    simp [e] at h2
    norm_num
    exact h1

  -- case n is odd
  .
    replace o: 2 ∣ n - 1 := by
      omega
    apply exists_eq_mul_right_of_dvd at o
    obtain ⟨k, hk⟩ := o
    specialize d k
    replace hk: n = 2 * k + 1 := by
      omega
    rw [← hk] at d
    rcases hn with ⟨h1, h2⟩
    rw [Nat.prime_dvd_prime_iff_eq] at d
    specialize l n (by omega)
    simp [d] at l
    norm_num
    exact h1
    

