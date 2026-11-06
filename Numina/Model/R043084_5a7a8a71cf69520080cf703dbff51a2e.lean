import Mathlib

theorem number_theory_4644 (a b m : ℤ) (_ : 0 < a) (h : a.gcd m = 1)
  (hr : a * r1 + b ≡ a * r2 + b [ZMOD m]) : r1 ≡ r2 [ZMOD m] := by
  have hm1 : (a * r1 + b : ℤ) % m = (a * r2 + b : ℤ) % m := by 
    exact hr
  -- Now that we have hm1 : (a * r1 + b) % m = (a * r2 + b) % m
  -- We can derive divisibility.
  have hm2 : m ∣ ((a * r2 + b : ℤ) - (a * r1 + b : ℤ)) := by 
    exact Int.dvd_of_emod_eq_zero (by 
      rw [Int.sub_emod]
      simp [hm1] 
      all_goals omega
    )
  have hm3 : m ∣ (a * (r2 - r1)) := by
    have h4 : ((a * r2 + b : ℤ) - (a * r1 + b : ℤ)) = a * (r2 - r1) := by 
      ring 
    have hm5 : m ∣ (a * (r2 - r1)) := by
      rw [h4] at hm2 
      exact hm2 
    exact hm5 
  -- m ∣ a * (r2 - r1). Using the condition a.gcd m = 1 to derive m ∣ (r2 - r1)
  have hm4 : IsCoprime m a := by 
    rw [Int.isCoprime_iff_gcd_eq_one] 
    have h5 : m.gcd a = 1 := by 
      rw [Int.gcd_comm] 
      exact h 
    exact h5 
  -- Now, using IsCoprime.dvd_of_dvd_mul_left
  have hm5 : m ∣ (r2 - r1) := by
    apply IsCoprime.dvd_of_dvd_mul_left hm4 
    exact hm3 
  -- Now that we have m ∣ (r2 - r1), we can show congruence
  have hm7 : r2 ≡ r1 [ZMOD m] := by 
    exact Int.modEq_of_dvd (by
      obtain ⟨k, hk⟩ := hm5
      use -k 
      linarith 
    )
  have h7 : r1 ≡ r2 [ZMOD m] := by 
    exact Int.ModEq.symm hm7 
  exact h7