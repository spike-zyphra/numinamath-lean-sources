import Mathlib

/-
If the least common multiple of $A$ and $B$ is $120$, and the ratio of $A$ to $B$ is $3:4$, then what is their greatest common divisor?
-/


set_option maxHeartbeats 300000
theorem number_theory_16337 {A B : ℕ} (h₀ : Nat.lcm A B = 120) (h₁ : A * 4 = B * 3) :
    Nat.gcd A B = 10 := by
    
    --Some basic facts.
    have Apos : 0 < A := by
      by_contra 
      have A0 : A = 0 := by linarith
      rw [A0] at h₀
      simp at h₀ 
    have gcdn0: Nat.gcd A B ≠ 0 := by
      refine Nat.gcd_ne_zero_left ?_
      omega
    have gcdnneg: 0 ≤  Nat.gcd A B := by exact Nat.zero_le (A.gcd B)
    have gcdpos : 0 < Nat.gcd A B := by omega


    --A simple claim directly from the assumptions: A = 3*(A,B) and B = 4*(A,B).
    have AgBg : A = 3 * Nat.gcd A B ∧ B = 4 * Nat.gcd A B := by
      have : Nat.gcd A B ∣ A := by exact Nat.gcd_dvd_left A B
      obtain ⟨a,ha⟩ := this
      have : Nat.gcd A B ∣ B := by exact Nat.gcd_dvd_right A B
      obtain ⟨b,hb⟩ := this
      have cp : Nat.Coprime a b := by
        have : 0 ≤ (Nat.gcd a b) := by exact Nat.zero_le (a.gcd b)
        have : Nat.gcd a b ≠ 0 := by 
          refine Nat.gcd_ne_zero_left ?_
          by_contra a0
          have : A = 0 := by rw [a0] at ha; simp at ha; exact ha
          linarith
        have : 0 < (Nat.gcd a b) := by omega

        have : Nat.gcd a b = 1 := by 
          have ad : Nat.gcd a b ∣ a := by exact Nat.gcd_dvd_left a b
          have bd : Nat.gcd a b ∣ b := by exact Nat.gcd_dvd_right a b
          obtain ⟨aa,haa⟩ := ad
          obtain ⟨bb,hbb⟩ := bd
          have : A = (Nat.gcd A B) * (Nat.gcd a b) * aa := by nlinarith
          have dA: (Nat.gcd a b) * (Nat.gcd A B) ∣ A := by use aa; nlinarith
          have : B = (Nat.gcd A B) * (Nat.gcd a b) * bb := by nlinarith
          have dB: (Nat.gcd a b) * (Nat.gcd A B) ∣ B := by use bb; nlinarith
          have : (Nat.gcd a b) * (Nat.gcd A B) ∣ Nat.gcd A B := by exact Nat.dvd_gcd dA dB
          apply Nat.le_of_dvd at this; 
          have : (Nat.gcd a b) ≤ 1 := by nlinarith
          omega
          exact gcdpos

        exact this

      rw [ha] at h₁
      nth_rw 2 [hb] at h₁
      have eq: 4*a = 3*b := by nlinarith
      have : a ∣ 3*b := by use 4; linarith
      have ad3: a ∣ 3 := by exact Nat.Coprime.dvd_of_dvd_mul_right cp this
      have p3: Nat.Prime 3 := by norm_num
      have : a = 1 ∨ a = 3 := by exact (Nat.dvd_prime p3).mp ad3
      rcases this with a1 | a3
      exfalso;
      rw [a1] at eq; omega
      have b4: b = 4 := by 
        rw [a3] at eq
        norm_num at eq;
        omega
      rw [a3] at ha; rw [b4] at hb
      rw [mul_comm] at ha hb
      tauto
        
    have Ag: A = 3 * Nat.gcd A B := by exact AgBg.left
    have Bg: B = 4 * Nat.gcd A B := by exact AgBg.right

    --Then we use that [A,B] * (A,B) = A * B to get (A,B).
    have eq: Nat.lcm A B * Nat.gcd A B = A * B := by 
      refine Eq.symm (Nat.eq_mul_of_div_eq_left ?_ rfl)
      have : Nat.gcd A B ∣ A := by exact Nat.gcd_dvd_left A B
      exact Dvd.dvd.mul_right this B
    rw [h₀] at eq
    nth_rw 2 [Ag] at eq
    nth_rw 3 [Bg] at eq
    
    have : Nat.gcd A B * (((Nat.gcd A B):ℤ) - 10) = 0 := by 
      zify at eq
      ring_nf at eq
      nlinarith
    have :((Nat.gcd A B):ℤ) = 0 ∨ ((Nat.gcd A B):ℤ) - 10 = 0:= by exact Int.mul_eq_zero.mp this
    simp [gcdn0] at this
    have : ((Nat.gcd A B):ℤ) = 10 := by linarith
    norm_cast at this

