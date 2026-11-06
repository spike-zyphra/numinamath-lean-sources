import Mathlib

/- What is the largest integer that is a divisor of
(n+1)(n+3)(n+5)(n+7)(n+9)
for all positive even integers n?
(A) 3(B) 5(C) 11(D) 15(E) 165-/
theorem number_theory_94886 : IsGreatest {x | ∀ n : ℕ, Even n → x ∣ (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9)} 15 := by {
  constructor

/- We will prove this in two steps. First we show that any even n
of the given form is divisible by 15. Then we show that every
integer with the property that it always divides (n+1)(n+3)(n+5)(n+7)(n+9)
when n is even has to be ≤ 15. We do that by contradiction, assuming that 
such a number is > 15 and proving False.
-/
  simp
  intros n hn
  have : 15 = 3*5 := by norm_num
  rw [this]
  -- We split the claim into showing that any such number is divible by 3 and by 5.
  apply Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
  mod_cases n % 3 -- Split according to the value of n [MOD 3].

  -- In each case, we can quickly show that one of the factors is
  -- divisible by 3 and deduce the claim.
  suffices : 3 ∣ (n + 3)
  apply Nat.dvd_trans this
  use (n + 1) * (n + 5) * (n + 7) * (n + 9)
  ring
  apply Nat.dvd_add
  rw [Nat.dvd_iff_mod_eq_zero]
  exact H
  trivial

  suffices : 3 ∣ (n + 5)
  apply Nat.dvd_trans this
  use (n + 1) * (n + 3) * (n + 7) * (n + 9)
  ring
  apply Nat.ModEq.add_right 5 at H
  unfold Nat.ModEq at H
  norm_num at H
  rw [Nat.dvd_iff_mod_eq_zero]
  exact H

  suffices : 3 ∣ (n + 1)
  apply Nat.dvd_trans this
  use (n + 3) * (n + 5) * (n + 7) * (n + 9)
  ring
  apply Nat.ModEq.add_right 1 at H
  unfold Nat.ModEq at H
  norm_num at H
  rw [Nat.dvd_iff_mod_eq_zero]
  exact H

  mod_cases n % 5 -- Now we do the same for 5.

  suffices : 5 ∣ (n + 5)
  apply Nat.dvd_trans this
  use (n + 1) * (n + 3) * (n + 7) * (n + 9)
  ring
  apply Nat.ModEq.add_right 5 at H
  unfold Nat.ModEq at H
  norm_num at H
  apply Nat.dvd_add
  rw [Nat.dvd_iff_mod_eq_zero]
  exact H
  trivial

  suffices : 5 ∣ (n + 9)
  apply Nat.dvd_trans this
  use (n + 1) * (n + 3) * (n + 5) * (n + 7)
  ring
  apply Nat.ModEq.add_right 9 at H
  unfold Nat.ModEq at H
  norm_num at H
  rw [Nat.dvd_iff_mod_eq_zero]
  exact H

  suffices : 5 ∣ (n + 3)
  apply Nat.dvd_trans this
  use (n + 1) * (n + 5) * (n + 7) * (n + 9)
  ring
  apply Nat.ModEq.add_right 3 at H
  unfold Nat.ModEq at H
  norm_num at H
  rw [Nat.dvd_iff_mod_eq_zero]
  exact H

  suffices : 5 ∣ (n + 7)
  apply Nat.dvd_trans this
  use (n + 1) * (n + 3) * (n + 5) * (n + 9)
  ring
  apply Nat.ModEq.add_right 7 at H
  unfold Nat.ModEq at H
  norm_num at H
  rw [Nat.dvd_iff_mod_eq_zero]
  exact H

  suffices : 5 ∣ (n + 1)
  apply Nat.dvd_trans this
  use (n + 3) * (n + 5) * (n + 7) * (n + 9)
  ring
  apply Nat.ModEq.add_right 1 at H
  unfold Nat.ModEq at H
  norm_num at H
  rw [Nat.dvd_iff_mod_eq_zero]
  exact H

  -- We now show the converse by contradiction
  intros n hn
  contrapose hn
  simp at hn
  simp

  /-We first assume that n has a prime divisor other than 3 or 5.
  -/
  by_cases hp : ∃ p : ℕ, Nat.Prime p ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ∣ n
  rcases hp with ⟨p,⟨hpp,hp3,hp5,hpdvd⟩⟩
  by_cases hp7 : p > 7 -- We further assume that that prime divisor is > 7.
  use 2*p -- In that case, we can quickly show that p can never divide the required product, by showing that it can't divide any of the factors. Thus, neither can n.
  simp
  intro hndvd
  apply Nat.dvd_trans hpdvd at hndvd
  rw [Nat.Prime.dvd_mul hpp,Nat.Prime.dvd_mul hpp,Nat.Prime.dvd_mul hpp,Nat.Prime.dvd_mul hpp] at hndvd
  rcases hndvd with (((hpdvd1 | hpdvd3) | hpdvd5) | hpdvd7) | hpdvd9
  
  rw [two_mul,add_assoc,Nat.dvd_add_self_left,Nat.dvd_add_self_left,Nat.dvd_one] at hpdvd1
  rw [hpdvd1] at hp7
  trivial

  rw [two_mul,add_assoc,Nat.dvd_add_self_left,Nat.dvd_add_self_left,Nat.prime_dvd_prime_iff_eq hpp (by trivial)] at hpdvd3
  rw [hpdvd3] at hp7
  trivial

  rw [two_mul,add_assoc,Nat.dvd_add_self_left,Nat.dvd_add_self_left,Nat.prime_dvd_prime_iff_eq hpp (by trivial)] at hpdvd5
  rw [hpdvd5] at hp7
  trivial

  rw [two_mul,add_assoc,Nat.dvd_add_self_left,Nat.dvd_add_self_left,Nat.prime_dvd_prime_iff_eq hpp (by trivial)] at hpdvd7
  rw [hpdvd7] at hp7
  trivial

  rw [two_mul,add_assoc,Nat.dvd_add_self_left,Nat.dvd_add_self_left] at hpdvd9
  have : 9 = 3*3 := by norm_num
  rw [this,Nat.Prime.dvd_mul hpp] at hpdvd9
  simp at hpdvd9
  rw [Nat.prime_dvd_prime_iff_eq hpp (by trivial)] at hpdvd9
  rw [hpdvd9] at hp7
  trivial

  -- We now treat the case when p ≤ 7. This can be done using a simple case distinction. The only cases of note are p = 7 and p = 2, where we can write down an explicit counterexample.
  simp at hp7
  match p with
    | 7 => {
      use 8
      simp
      constructor
      trivial
      intro hn1
      have := Nat.dvd_trans hpdvd hn1
      trivial
    }
    | 6 => trivial
    | 5 => trivial
    | 4 => trivial
    | 3 => trivial
    | 2 => {
      use 2
      simp
      intro hn1
      have := Nat.dvd_trans hpdvd hn1
      trivial
    }
    | 1 => trivial
    | 0 => trivial
    | m + 8 => trivial


  simp at hp
  -- We now have the case left when all prime divisors of n are either 3 or 5. We will next show that since n > 15 (and thus not n ∣ 15), we must have 9 ∣ n or 25 ∣ n. This is a slightly tedious proof using prime factorisations.
  have hn' : 9 ∣ n ∨ 25 ∣ n := by {
    by_contra hndvd
    simp at hndvd
    rcases hndvd with ⟨hn9,hn25⟩ 
    suffices : n ∣ 15
    apply Nat.le_of_dvd (by trivial) at this
    linarith
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intros p k hpp hpkdvd
    have := hp p hpp
    by_cases hp3 : p = 3
    rw [hp3]
    have hk1 : k ≤ 1 := by {
      contrapose hpkdvd
      simp at hpkdvd
      rw [hp3]
      intro h3kdvd
      have : 9 ∣ 3 ^ k := by {
        rw [Nat.dvd_prime_pow (by trivial)]
        use 2
        simp
        linarith
      }
      have := Nat.dvd_trans this h3kdvd
      trivial
    }
    rcases hk1 with hk1 | hk0
    trivial
    simp at hk0
    rw [hk0]
    trivial

    have := this hp3
    by_cases hp5 : p = 5

    rw [hp5]
    have hk1 : k ≤ 1 := by {
      contrapose hpkdvd
      simp at hpkdvd
      rw [hp5]
      intro h5kdvd
      have : 25 ∣ 5 ^ k := by {
        rw [Nat.dvd_prime_pow (by trivial)]
        use 2
        simp
        linarith
      }
      have := Nat.dvd_trans this h5kdvd
      trivial
    }
    rcases hk1 with hk1 | hk0
    trivial
    simp at hk0
    rw [hk0]
    trivial

    have := this hp5
    suffices : k = 0
    rw [this]
    simp

    contrapose! this
    have hpdvd : p ∣ p^k := by {
      rw [Nat.dvd_prime_pow (by trivial)]
      use 1
      simp
      rw [←Nat.one_le_iff_ne_zero] at this
      exact this
    }
    exact Nat.dvd_trans hpdvd hpkdvd
  }

  -- We can now assume that 9 ∣ n or 25 ∣ n. In each case, we can give an explicit counterexample to the claimed divisibility property.
  rcases hn' with hn9 | hn25
  use 10
  constructor
  trivial
  intro hndvd
  have := Nat.dvd_trans hn9 hndvd 
  trivial

  use 10
  constructor
  trivial
  intro hndvd
  have := Nat.dvd_trans hn25 hndvd 
  trivial
}