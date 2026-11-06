import Mathlib

/-Suppose $t$ is a positive integer such that $\mathop{\text{lcm}}[12,t]^3=(12t)^2$. What is the smallest possible value for $t$?-/
theorem number_theory_19167 :
    IsLeast {t : ℕ | 0 < t ∧ (Nat.lcm 12 t) ^ 3 = (12 * t) ^ 2} 18 := by
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  -- easily verify that 18 can be the answer
  . norm_num
  -- prove the main part of the problem
  . intro t ht hlcm
    -- show that gcd 12 t * lcm 12 t = 12 * t
    have eq : Nat.gcd 12 t * Nat.lcm 12 t = 12 * t := by
      rw [Nat.gcd_mul_lcm]
    -- show that lcm 12 t ^ 3 > 0, so that we can do calculation
    have hlcm0 : Nat.lcm 12 t ^ 3 > 0 := by
      calc
        Nat.lcm 12 t ^ 3 = (12 * t) ^ 2 := by rw [hlcm]
        _ > 0 := by positivity

    -- show that gcd 12 t ^ 3 = 12 * t, crucial expression
    have hgcd : Nat.gcd 12 t ^ 3 = 12 * t := by
      calc
        Nat.gcd 12 t ^ 3 = (Nat.gcd 12 t) ^ 3 * (Nat.lcm 12 t) ^ 3 / Nat.lcm 12 t ^ 3 := by rw [Nat.mul_div_cancel]; linarith only [hlcm0]
        _ = (Nat.gcd 12 t * Nat.lcm 12 t) ^ 3 / Nat.lcm 12 t ^ 3 := by ring_nf
        _ = (12 * t) ^ 3 / (12 * t) ^ 2 := by rw [hlcm, eq]
        _ = (12 * t) * (12 * t) ^ 2 / (12 * t) ^ 2 := by ring_nf
        _ = 12 * t := by rw [Nat.mul_div_cancel]; nlinarith only [ht]
    -- show that 2 ∣ gcd 12 t
    have hgcd2 : 2 ∣ 12 * t := by use (6 * t); ring_nf
    rw [<-hgcd] at hgcd2
    apply Nat.Prime.dvd_of_dvd_pow at hgcd2
    pick_goal 2
    norm_num
    -- show that 3 ∣ gcd 12 t
    have hgcd3 : 3 ∣ 12 * t := by use (4 * t); ring_nf
    rw [<-hgcd] at hgcd3
    apply Nat.Prime.dvd_of_dvd_pow at hgcd3
    pick_goal 2
    norm_num
    -- combine both of above, so that we have 6 ∣ gcd 12 t
    have hgcd6 : 2 * 3 ∣ Nat.gcd 12 t := by
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      norm_num
      exact hgcd2
      exact hgcd3
    clear hgcd2 hgcd3
    -- by dvd, we have 6 ≤ gcd 12 t (for gcd 12 t > 0)
    apply Nat.le_of_dvd at hgcd6
    pick_goal 2
    nlinarith
    -- show that 6 ^ 3 ≤ gcd 12 t ^ 3
    replace hgcd6 : 6 ^ 3 ≤ Nat.gcd 12 t ^ 3 := by
      apply Nat.pow_le_pow_left
      linarith only [hgcd6]
    -- finally get the answer
    rw [hgcd] at hgcd6
    linarith only [hgcd6]