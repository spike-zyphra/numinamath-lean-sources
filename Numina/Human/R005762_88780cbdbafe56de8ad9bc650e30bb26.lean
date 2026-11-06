import Mathlib

/- Distinct prime numbers $p, q, r$ satisfy the equation
$$
2 p q r+50 p q=7 p q r+55 p r=8 p q r+12 q r=A
$$
for some positive integer $A$. What is $A$ ?-/
theorem number_theory_609785 : {A :ℕ | ∃ p q r : ℕ, (Nat.Prime p) ∧ (Nat.Prime q) ∧ (Nat.Prime r) ∧ (p ≠ q ∧ q ≠ r ∧ r ≠ p)
  ∧ (0 < A) ∧ (2 * p * q * r + 50 * p * q = A) ∧ (7 * p * q * r + 55 * p * r = A) ∧
  (8 * p * q * r + 12 * q * r = A)} = {1980} := by
  -- Answer: 1980
  apply Set.ext
  intro A ;simp
  constructor
  intro ⟨p,hp,q,hq,r,hr,hpqr,hA1,hA2,hA3,hA4⟩
  -- Note that $A$ is a multiple of $p, q$, and $r$, so $K=\frac{A}{p q r}$ is an integer.
  have h1 : (p * q * r) ∣ A := by
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ ?_
    refine Nat.Coprime.mul ?_ ?_
    apply (Nat.coprime_primes hp hr).mpr
    exact id (Ne.symm hpqr.2.2)
    apply (Nat.coprime_primes hq hr).mpr
    exact hpqr.2.1
    rw [← hA2,mul_comm (2 * p * q),← mul_assoc,← mul_assoc,mul_assoc,mul_assoc 50,← add_mul]
    exact Nat.dvd_mul_left (p * q) (r * 2 + 50)
    rw [← hA3,← add_mul]
    exact Nat.dvd_mul_left r (7 * p * q + 55 * p)
  rcases exists_eq_mul_left_of_dvd h1 with ⟨K,hK⟩
  -- Dividing through, we have that $$ K=8+\frac{12}{p}=7+\frac{55}{q}=2+\frac{50}{r} $$
  replace hA2 : 2 * r + 50 = K * r := by
    rw [hK] at hA2 ;ring_nf at hA2 ;rw [mul_assoc (p*q),← mul_add,mul_assoc (p*q)] at hA2
    simp [Nat.Prime.ne_zero hp,Nat.Prime.ne_zero hq] at hA2
    ring_nf ;exact hA2
  replace hA3 : 7 * q + 55 = K * q := by
    rw [hK,mul_assoc 55,mul_assoc 7,mul_comm p,← mul_assoc,mul_assoc,← add_mul,mul_assoc,← mul_assoc K] at hA3
    simp [Nat.Prime.ne_zero hp,Nat.Prime.ne_zero hr] at hA3 ;exact hA3
  replace hA4 : 8 * p + 12 = K * p := by
    rw [mul_assoc,hK,mul_assoc 12,← add_mul,mul_assoc,← mul_assoc K] at hA4
    simp [Nat.Prime.ne_zero hq,Nat.Prime.ne_zero hr] at hA4 ;exact hA4
  -- Then $p \in\{2,3\}, q \in\{5,11\}$, and $r \in\{2,5\}$.
  have hp' : p = 2 ∨ p = 3 := by
    have : p ∣ (8 * p + 12) := by rw [hA4] ;simp
    apply (Nat.dvd_add_right (by simp)).mp at this
    have this' : 12 = 2 * 2 * 3 := by norm_num
    rw [this'] at this ; apply (Nat.Prime.dvd_mul hp).mp at this
    rcases this with this | this
    · apply (Nat.Prime.dvd_mul hp).mp at this ;simp at this ;apply (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_two)).mp at this ;simp [this]
    apply (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_three)).mp at this ;simp [this]
  have hq' : q = 5 ∨ q = 11 := by
    have : q ∣ (7 * q + 55) := by rw [hA3] ;simp
    apply (Nat.dvd_add_right (by simp)).mp at this
    have this' : 55 = 5 * 11 := by norm_num
    rw [this'] at this ; apply (Nat.Prime.dvd_mul hq).mp at this
    rcases this with this | this
    · apply (Nat.prime_dvd_prime_iff_eq hq (Nat.prime_five)).mp at this ;simp [this]
    apply (Nat.prime_dvd_prime_iff_eq hq (Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl)).mp at this ;simp [this]
  have hr' : r = 2 ∨ r = 5 := by
    have : r ∣ (2 * r + 50) := by rw [hA2] ;simp
    apply (Nat.dvd_add_right (by simp)).mp at this
    have this' : 50 = 5 * 5 * 2 := by norm_num
    rw [this'] at this ; apply (Nat.Prime.dvd_mul hr).mp at this
    rcases this with this | this
    · apply (Nat.Prime.dvd_mul hr).mp at this ;simp at this ;apply (Nat.prime_dvd_prime_iff_eq hr (Nat.prime_five)).mp at this ;simp [this]
    apply (Nat.prime_dvd_prime_iff_eq hr (Nat.prime_two)).mp at this ;simp [this]
  -- These values give $K \in\{14,12\}, K \in\{18,12\}$, and $K \in$ $\{27,12\}$,
  -- giving $K=12$ and $(p, q, r)=(3,11,5)$.
  rcases hp' with hp' | hp'
  · rw [hp'] at hA4 ;norm_num at hA4
    have : K * 2 = 14 * 2 := by rw [← hA4]
    apply Nat.eq_of_mul_eq_mul_right (by simp) at this
    rcases hq' with hq' | hq'
    · rw [hq',this] at hA3 ;norm_num at hA3
    rw [hq',this] at hA3 ;norm_num at hA3
  rw [hp'] at hA4 ;norm_num at hA4
  have : K * 3 = 12 * 3 := by rw [← hA4]
  apply Nat.eq_of_mul_eq_mul_right (by simp) at this
  rcases hq' with hq' | hq'
  rw [hq',this] at hA3 ;norm_num at hA3
  rcases hr' with hr' | hr'
  rw [hr',this] at hA2 ;norm_num at hA2
  rw [hK,hp',hq',hr',this] ;norm_num
  intro hA
  use 3 ;norm_num ;use 11 ;norm_num ;use 5 ;norm_num ;simp [hA]