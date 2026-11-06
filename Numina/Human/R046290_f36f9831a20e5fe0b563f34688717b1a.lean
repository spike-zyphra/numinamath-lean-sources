import Mathlib

/- It is known that, for all positive integers k,
1^2+2^2+3^2+…+k^2=k(k+1)(2k+1)/6​.
Find the smallest positive integer k such that 1^2+2^2+3^2+…+k^2 is a multiple of 200. -/
theorem number_theory_98037 :
IsLeast {k : ℕ | 0 < k ∧ 200 ∣ ∑ i in Finset.Icc 1 k, i ^ 2} 112 := by {
  -- We start by showing the formula for the sum of the squares by induction. This is straight-forward.
  have h₁ (k : ℕ) : 6*(∑ i in Finset.Icc 1 k, i ^ 2) = k*(k+1)*(2*k+1) := by induction k with 
  | zero => {
    trivial
  }
  | succ k hk => {
    rw [Finset.sum_Icc_succ_top (by linarith),mul_add,hk]
    ring
  }
  -- We need to show that 112 is the smallest number such that the sum is divisible by 200. We split this into showing
  -- that 112 has the desired divisibility condition, and then that any number with the desired condition is at least 112.
  constructor
  -- We now show the first part, which is immediate
  simp
  have h₂ : ∑ i ∈ Finset.Icc 1 112, i ^ 2 = 474600 := by {
    calc ∑ i ∈ Finset.Icc 1 112, i ^ 2 = (6 * ∑ i ∈ Finset.Icc 1 112, i ^ 2) / 6 := by trivial
                                     _ = 474600 := by rw [h₁]
  }
  rw [h₂]
  trivial

  -- For the second part, we use the formula we proved for the sum over the squares, so we need to understand when
  -- 1200 ∣ k*(k+1)*(2*k+1)

  unfold lowerBounds
  simp

  intros k hk0 hk
  have : 6 ∣ 6 := by trivial
  apply mul_dvd_mul (this) at hk
  rw [h₁] at hk
  simp at hk

  -- We now proceed to show that k has to satisfy congruence conditions modulo 16 and 25. These congruence conditions
  -- will be enough to deduce the claim because they will immediately force k ≥ 112.

  have h₃ : k % 16 = 0 ∨ k % 16 = 15 := by {
    -- To show the congruence condition modulo 16, note that 2*k+1 is always odd, so we only need to look at what the condition
    -- 16 ∣ k*(k+1) implies. Since one of them is always odd, this means that the other one has to be divisible by 16, which gives
    -- k ≡ 0,15 [MOD 16]
    have hk' : 16 ∣ k*(k+1) := by {
      have : 1200 = 16 * 75 := by norm_num
      rw [this] at hk
      apply dvd_of_mul_right_dvd at hk
      rw [←Nat.dvd_gcd_mul_gcd_iff_dvd_mul] at hk
      have h2kp1 : Nat.gcd 16 (2*k+1) = 1 := by {
        have : 16 = 2^4 := by norm_num
        rw [this,←Nat.coprime_iff_gcd_eq_one,Nat.coprime_pow_left_iff (by trivial),add_comm,Nat.coprime_add_mul_left_right]
        trivial
      }
      rw [h2kp1] at hk
      simp at hk
      rw [Nat.dvd_gcd_iff] at hk
      simp at hk
      exact hk
    }
    mod_cases hk2 : k % 2
    rw [←Nat.dvd_gcd_mul_gcd_iff_dvd_mul] at hk'
    have : Nat.gcd 16 (k+1) = 1 := by {
      have : 16 = 2^4 := by norm_num
      rw [this,←Nat.coprime_iff_gcd_eq_one,Nat.coprime_pow_left_iff (by trivial),Nat.coprime_two_left,Nat.odd_add_one,Nat.not_odd_iff]
      trivial
    }
    rw [this] at hk'
    simp at hk'
    rw [Nat.dvd_gcd_iff] at hk'
    simp at hk'
    omega

    rw [←Nat.dvd_gcd_mul_gcd_iff_dvd_mul] at hk'
    have : Nat.gcd 16 k = 1 := by {
      have : 16 = 2^4 := by norm_num
      rw [this,←Nat.coprime_iff_gcd_eq_one,Nat.coprime_pow_left_iff (by trivial),Nat.coprime_two_left,Nat.odd_iff]
      trivial
    }
    rw [this] at hk'
    simp at hk'
    rw [Nat.dvd_gcd_iff] at hk'
    simp at hk'
    omega
  }
  have h₄ : k % 25 = 0 ∨ k % 25 = 12 ∨ k % 25 = 24 := by {
    -- To show the congruence condition modulo 25, note that 25 ∣ k*(k+1)*(2*k+1) actually implies that one of these three
    -- factors has to be divisible by 25, since by coprimality no two of the factors can be divisible by 5 simulaneously.
    -- This then implies that k ≡ 0,12,24 [MOD 25].
    have hk' : 25 ∣ k*(k+1)*(2*k+1) := by {
      have : 1200 = 25 * 48 := by norm_num
      rw [this] at hk
      apply dvd_of_mul_right_dvd at hk
      exact hk
    }
    suffices : 25 ∣ k ∨ 25 ∣ (k+1) ∨ 25 ∣ (2*k+1)
    omega
    have : 25 = 5*5 := by trivial
    
    have hk5 : 5 ∣ k ∨ 5 ∣ k+1 ∨ 5 ∣ (2*k+1) := by {
      rw [←Nat.Prime.dvd_mul (by trivial),←Nat.Prime.dvd_mul (by trivial),←mul_assoc]
      have : 5 ∣ 25 := by trivial
      apply Nat.dvd_trans this
      exact hk'
    }
    rcases hk5 with ⟨n,hk50⟩ | ⟨n,hk54⟩ | ⟨n,hk52⟩
    rw [hk50] at hk'
    rw [this] at hk'
    rw [mul_assoc,mul_assoc,Nat.mul_dvd_mul_iff_left (by trivial)] at hk'
    left
    rw [hk50,this,Nat.mul_dvd_mul_iff_left (by trivial)]
    rw [Nat.Prime.dvd_mul (by trivial),Nat.Prime.dvd_mul (by trivial)] at hk'
    omega

    right; left
    rw [hk54,this,Nat.mul_dvd_mul_iff_left (by trivial)]
    have hk54' : k = 5*n - 1 := by omega
    rw [hk54,hk54',mul_assoc,mul_comm,this,mul_assoc,mul_assoc,Nat.mul_dvd_mul_iff_left (by trivial),Nat.Prime.dvd_mul (by trivial),Nat.Prime.dvd_mul (by trivial)] at hk'
    omega
    
    right; right
    rw [hk52,this,Nat.mul_dvd_mul_iff_left (by trivial)]
    rw [hk52,mul_comm,mul_assoc,this,Nat.mul_dvd_mul_iff_left (by trivial),Nat.Prime.dvd_mul (by trivial),Nat.Prime.dvd_mul (by trivial)] at hk'
    omega
  }

  -- The claimed inequality k ≥ 112 follows immediately from the above congruence conditions.
  omega
}