import Mathlib

theorem algebra_11511 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c) (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 3 + a * x ^ 2 + b * x + c)
    (h1 : f (a : ℝ) = a ^ 3) (h2 : f (b : ℝ) = b ^ 3) :
    a + b + c = 18 := by
  have eq1 : (a : ℝ) ^ 3 + a * (a : ℝ) ^ 2 + b * (a : ℝ) + c = (a : ℝ) ^ 3 := by
    have h1' : f (a : ℝ) = (a : ℝ) ^ 3 + a * (a : ℝ) ^ 2 + b * (a : ℝ) + c := by
      apply hf
    rw [h1'] at h1
    linarith
  have eq1' : a * (a : ℝ) ^ 2 + b * (a : ℝ) + c = 0 := by
    ring_nf at eq1 ⊢
    linarith
  have eq2 : (b : ℝ) ^ 3 + a * (b : ℝ) ^ 2 + b * (b : ℝ) + c = (b : ℝ) ^ 3 := by
    have h2' : f (b : ℝ) = (b : ℝ) ^ 3 + a * (b : ℝ) ^ 2 + b * (b : ℝ) + c := by
      apply hf
    rw [h2'] at h2
    linarith
  have eq2' : a * (b : ℝ) ^ 2 + (b : ℝ) * (b : ℝ) + (c : ℝ) = 0 := by
    ring_nf at eq2 ⊢
    linarith
  have eq1'' : a ^ 3 + a * b + c = 0 := by
    have eq1'_int : a * (a : ℝ) ^ 2 + b * (a : ℝ) + c = 0 := by
      linarith
    have eq1'_int' : (a ^ 3 + a * b + c : ℝ) = 0 := by 
      ring_nf at eq1'_int ⊢
      linarith
    exact_mod_cast eq1'_int'
  have eq2'' : a * b ^ 2 + b ^ 2 + c = 0 := by
    have eq2'_int : a * (b : ℝ) ^ 2 + (b : ℝ) * (b : ℝ) + (c : ℝ) = 0 := by 
      linarith
    have eq2'_int' : (a * b ^ 2 + b ^ 2 + c : ℝ) = 0 := by 
      ring_nf at eq2'_int ⊢
      linarith
    exact_mod_cast eq2'_int'
  have eq3 : a ^ 3 + a * b + c = 0 := eq1''
  have eq4 : a * b ^ 2 + b ^ 2 + c = 0 := eq2''
  have eq5 : a ^ 3 + a * b = a * b ^ 2 + b ^ 2 := by 
    nlinarith
  have eq6 : (a - b) * (a ^ 2 + a * b + b) = 0 := by
    nlinarith
  have ha2 : a ^ 2 + a * b + b = 0 := by 
    apply (mul_left_inj' (show (a - b : ℤ) ≠ 0 by 
      intro h
      apply hdist.1
      omega
    )).mp
    linarith
  have ha_eq : a = -2 := by
    have h : a + 1 ≠ 0 := by
      by_contra h'
      have h_a_eq : a = -1 := by
        omega
      rw [h_a_eq] at ha2
      nlinarith
    have ha3 : a ^ 2 = -b * (a + 1) := by 
      nlinarith
    have ha5 : (a + 1) ∣ a ^ 2 := by
      use -b
      linarith
    have h' : (a + 1) ∣ 1 := by
      have ha8 : (a + 1) ∣ a ^ 2 := ha5
      have ha9 : (a + 1) ∣ (a + 1) * (a - 1) := by
        use a - 1
        all_goals ring
      have ha10 : (a + 1) ∣ (a ^ 2 - (a + 1) * (a - 1)) := by
        apply Dvd.dvd.sub
        exact ha8
        exact ha9
      have ha14 : (a ^ 2 - (a + 1) * (a - 1) : ℤ) = 1 := by
        nlinarith
      rw [ha14] at ha10
      exact ha10
    have h10 : (a + 1) = 1 ∨ (a + 1) = -1 := by 
      have h11 : (a + 1) ∣ 1 := h'
      have : (a + 1) = 1 ∨ (a + 1) = -1 := by 
        have h77 : (a + 1) ∣ 1 := h11
        have h88 : (a + 1) ≤ 1 := by 
          apply Int.le_of_dvd (show 0 < (1 : ℤ) by norm_num) h77
        have h100 : -1 ≤ (a + 1) := by 
          have h100 : -(a + 1) ∣ 1 := by 
            exact Int.neg_dvd.2 h77
          have h111 : -(a + 1) ≤ 1 := by 
            apply Int.le_of_dvd (show 0 < (1 : ℤ) by norm_num) h100
          linarith
        interval_cases h : (a + 1) <;> tauto
      tauto
    rcases h10 with h11 | h11
    · -- case (a + 1) = 1
      have ha0 : a = 0 := by 
        omega
      contradiction
    · -- case (a + 1) = -1
      have ha100 : a = -2 := by
        omega
      exact ha100
  have hb_eq : b = 4 := by
    rw [ha_eq] at ha2
    nlinarith
  have hc_eq : c = 16 := by
    rw [ha_eq, hb_eq] at eq1''
    nlinarith
  omega