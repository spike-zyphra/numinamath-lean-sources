import Mathlib

theorem algebra_110514 {a b c : ℤ} {f : ℤ → ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c) (hf : ∀ x, f x = x^3 + a * x^2 + b * x + c)
    (h1 : f a = a^3) (h2 : f b = b^3) : a = -2 ∧ b = 4 ∧ c = 16 := by

  have e1 : a ^ 3 + a * b + c = 0 := by rw [hf] at h1; linarith only [h1]
  have e2 : a * b ^ 2 + b ^ 2 + c = 0 := by rw [hf] at h2; linarith only [h2]

  have e3 : (a + 1) * b ^ 2 - a * b - a ^ 3 = 0 := by linear_combination e2 - e1
  have e4 : (a + 1) * b + a ^ 2 = 0 := by
    have : (b - a) * ((a + 1) * b + a ^ 2) = 0 := by rw [← e3]; ring
    cases' (mul_eq_zero.mp this) with h h
    · exfalso
      have h12 : a = b := by linarith
      have h13 : a ≠ b := hdist.1
      exact h13 (by linarith)
    · linarith

  have eq1 : (a + 1) * b = -a ^ 2 := by linarith [e4]
  have h7 : a + 1 ∣ a ^ 2 := by 
    use -b
    all_goals
      linarith [eq1]

  have h14 : (a + 1) ∣ 1 := by 
    have h8 : (a + 1) ∣ a ^ 2 := h7 
    have h42 : (a + 1) ∣ (a + 1) * (a - 1) := by 
      simp 
    have h43 : (a + 1) ∣ ( (a + 1) * (a - 1) + 1 ) := by
      have h22 : ( (a + 1) * (a - 1) + 1 ) = a ^ 2 := by 
        ring
      rw [h22]
      exact h8
    have h44 : ( (a + 1) * (a - 1) + 1 ) - ( (a + 1) * (a - 1) ) = 1 := by 
      nlinarith
    have h45 : (a + 1) ∣ ( (a + 1) * (a - 1) ) := h42
    have h46 : (a + 1) ∣ ( ( (a + 1) * (a - 1) + 1 ) - ( (a + 1) * (a - 1) ) ) := by 
      apply Dvd.dvd.sub 
      · exact h43 
      · exact h45
    have h47 : ( ( (a + 1) * (a - 1) + 1 ) - ( (a + 1) * (a - 1) ) ) = 1 := h44
    rw [h47] at h46
    assumption

  -- Now `(a + 1) ∣ 1` implies `(a + 1) = 1 or -1`.
  have h15 : (a + 1) = 1 ∨ (a + 1) = -1 := by
    have h14 : (a + 1) ∣ 1 := h14
    have : (a + 1) ≤ 1 := by apply Int.le_of_dvd (by norm_num) h14
    have : (a + 1) ≥ -1 := by
      have h5 : -(a + 1) ∣ 1 := by
        exact Int.neg_dvd.2 h14
      have h7 : -(a + 1) ≤ 1 := by apply Int.le_of_dvd (by norm_num) h5
      omega
    interval_cases h : (a + 1) <;> tauto

  cases h15 with
  | inl h16 =>
    have h10 : a = 0 := by linarith
    contradiction
  | inr h17 =>
    have h11 : a = -2 := by linarith
    have h12 : b = 4 := by
      rw [h11] at eq1
      omega
    have h13 : c = 16 := by
      rw [h11, h12] at e1
      omega
    exact ⟨by omega, by omega, by omega⟩