import Mathlib

theorem number_theory_29735 (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (hab : Nat.gcd a b = 1) (x y : ℤ) (hxy : a * x + b * y = a ^ n + b ^ n) :
    ⌊(x / b : ℝ)⌋ + ⌊(y / a : ℝ)⌋ = ⌊(a ^ (n - 1) / b : ℝ)⌋ + ⌊(b ^ (n - 1) / a : ℝ)⌋ := by 
  have h1 : (a : ℤ) * x + (b : ℤ) * y = (a : ℤ) ^ n + (b : ℤ) ^ n := by exact_mod_cast hxy
  have h2 : (a : ℤ) * (x - (a : ℤ) ^ (n - 1)) = (b : ℤ) * ((b : ℤ) ^ (n - 1) - y) := by
    cases n with
    | zero =>
      exfalso
      omega
    | succ n =>
      simp [pow_succ, pow_zero, mul_add, mul_assoc] at h1 ⊢
      all_goals
        ring_nf at h1 ⊢
        nlinarith
  have h4 : (a : ℤ) ∣ (b : ℤ) * ((b : ℤ) ^ (n - 1) - y) := by 
    use (x - (a : ℤ) ^ (n - 1))
    linarith [h2]
  have h5 : IsCoprime (a : ℤ) (b : ℤ) := by
    have hb1 : Nat.gcd a b = 1 := hab
    exact Int.coprime_iff_nat_coprime.mpr hb1
  have h6 : (a : ℤ) ∣ ((b : ℤ) ^ (n - 1) - y) := by
    have h7 : (a : ℤ) ∣ (b : ℤ) * ((b : ℤ) ^ (n - 1) - y) := h4
    have h7a : IsCoprime (a : ℤ) (b : ℤ) := h5
    apply IsCoprime.dvd_of_dvd_mul_left h7a h7
  obtain ⟨k, hk⟩ := h6
  have hk_eq : (b : ℤ) ^ (n - 1) - y = (a : ℤ) * k := by linarith
  have hk_eq' : (y : ℤ) = (b : ℤ) ^ (n - 1) - (a : ℤ) * k := by linarith
  have hk_eq2 : (x : ℤ) - (a : ℤ) ^ (n - 1) = (b : ℤ) * k := by
    have h11 : (a : ℤ) * (x - (a : ℤ) ^ (n - 1)) = (b : ℤ) * ((b : ℤ) ^ (n - 1) - y) := h2
    rw [show (b : ℤ) ^ (n - 1) - y = (a : ℤ) * k by linarith] at h11
    have h14 : (a : ℤ) * (x - (a : ℤ) ^ (n - 1)) = (a : ℤ) * (b * k : ℤ) := by
      linarith
    have ha' : (a : ℤ) ≠ 0 := by 
      have ha' : 0 < (a : ℤ) := by
        exact_mod_cast show (0 : ℕ) < a by linarith
      linarith
    have h13 : (x : ℤ) - (a : ℤ) ^ (n - 1) = (b * k : ℤ) := by 
      apply (mul_left_inj' ha').mp 
      linarith
    exact h13
  have hk_eq3 : (x : ℤ) = (a : ℤ) ^ (n - 1) + (b : ℤ) * k := by linarith
  have hk_eq4 : ⌊(x / b : ℝ)⌋ = ⌊(a ^ (n - 1) / b : ℝ)⌋ + k := by 
    have hk_eq4' : (x : ℝ) = (a ^ (n - 1) : ℝ) + (b * (k : ℝ) : ℝ) := by
      exact_mod_cast hk_eq3
    have hk_eq5' : (x / b : ℝ) = (a ^ (n - 1) / b : ℝ) + (k : ℝ) := by 
      rw [hk_eq4']
      field_simp
      all_goals
        ring_nf
    rw [hk_eq5']
    simp [Int.floor_add_int]
  have hk_eq5 : ⌊(y / a : ℝ)⌋ = ⌊(b ^ (n - 1) / a : ℝ)⌋ - k := by 
    have hk_eq6' : (y : ℝ) = (b ^ (n - 1) : ℝ) - (a * (k : ℝ) : ℝ) := by
      exact_mod_cast hk_eq'
    have hk_eq7' : (y / a : ℝ) = (b ^ (n - 1) / a : ℝ) - (k : ℝ) := by 
      rw [hk_eq6']
      field_simp
      all_goals
        ring_nf
    rw [hk_eq7']
    simp [Int.floor_sub_int]
  linarith [hk_eq4, hk_eq5]