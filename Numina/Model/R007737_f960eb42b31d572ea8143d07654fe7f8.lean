import Mathlib

theorem number_theory_22769 {A B : ℕ} (h₀ : Nat.lcm A B = 1575) (h₁ : A * 7 = B * 3) :
    Nat.gcd A B = 75 := by
  have h5 : 3 ∣ A := by
    have h6 : A * 7 % 3 = 0 := by
      omega
    have h7 : A % 3 = 0 := by
      omega
    exact Nat.dvd_of_mod_eq_zero h7
  rcases h5 with ⟨k, hk⟩
  have h10 : B = 7 * k := by 
    nlinarith [h₁, hk]
  have h13 : Nat.gcd A B = k := by
    rw [show A = 3 * k by linarith [hk], show B = 7 * k by linarith [h10]]
    have h14 : (3 * k).gcd (7 * k) = k := by
      have h15 : (3 * k).gcd (7 * k) = (3).gcd (7) * k := by
        rw [Nat.gcd_mul_right]
        all_goals omega
      have h16 : (3).gcd (7) = 1 := by
        norm_num
      rw [h16] at h15
      linarith
    linarith
  have h19 : k = 75 := by
    have h20 : Nat.lcm A B = 21 * k := by
      rw [show A = 3 * k by linarith [hk], show B = 7 * k by linarith [h10]]
      have h21 : (3 * k).lcm (7 * k) = 21 * k := by
        have h22 : (3 * k).lcm (7 * k) = (3).lcm (7) * k := by
          rw [Nat.lcm_mul_right]
          all_goals omega
        have h23 : (3).lcm (7) = 21 := by
          norm_num [Nat.lcm]
        rw [h23] at h22
        omega
      linarith
      all_goals omega
    linarith [h₀, h20]
  linarith [h13, h19]