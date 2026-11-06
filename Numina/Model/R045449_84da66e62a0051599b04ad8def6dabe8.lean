import Mathlib


theorem number_theory_151634 (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : Nat.Coprime x y) (hyz : Nat.Coprime y z) (hzz : Nat.Coprime x z)
    (h : (1 / x : ℚ) + 1 / y = 1 / z) :
    IsSquare (x - z) ∧ IsSquare (y - z) ∧ IsSquare (y + x) := by
  have eq1 : (x : ℚ) > 0 := by exact_mod_cast show (0 : ℕ) < x by linarith
  have eq2 : (y : ℚ) > 0 := by exact_mod_cast show (0 : ℕ) < y by linarith
  have eq3 : (z : ℚ) > 0 := by exact_mod_cast show (0 : ℕ) < z by linarith
  have h_eq : (x : ℚ) * (y : ℚ) = (x : ℚ) * (z : ℚ) + (y : ℚ) * (z : ℚ) := by 
    field_simp at h ⊢
    nlinarith
  have h_eq2 : (x : ℕ) * (y : ℕ) = (x : ℕ) * (z : ℕ) + (y : ℕ) * (z : ℕ) := by
    exact_mod_cast h_eq
  have h_eq3 : z ∣ x * y := by
    use x + y
    linarith [h_eq2]
  have h_eq4 : z = 1 := by
    have h1 : z ∣ x * y := h_eq3
    have h2 : Nat.Coprime z x := by
      exact Nat.Coprime.symm hzz
    have h3 : Nat.Coprime z y := by
      exact Nat.Coprime.symm hyz
    have h4 : z = 1 := by
      have h8 : z ∣ x * y := h1
      have h14 : Nat.Coprime z (x * y) := by
        have h15 : Nat.Coprime z x := h2
        have h16 : Nat.Coprime z y := h3
        exact Nat.Coprime.mul_right h15 h16
      have h15 : z = 1 := by
        exact Nat.Coprime.eq_one_of_dvd h14 h8
      exact h15
    exact h4
  have h_eq5 : x * y = x + y := by
    rw [show z = 1 by linarith [h_eq4] ] at h_eq2
    nlinarith
  have h_eq7 : x ∣ y := by
    have h17 : x ∣ x + y := by
      have h13 : x * y = x + y := by
        nlinarith
      have h14 : x ∣ x * y := by
        use y
        all_goals nlinarith
      rw [show x * y = x + y by linarith] at h14
      exact h14
    have h12 : x ∣ x := by
      exact dvd_refl x
    have h14 : x ∣ (x + y) - x := by
      apply Nat.dvd_sub'
      · exact h17
      · exact h12
    have h14' : x ∣ y := by
      have : (x + y) - x = y := by
        omega
      rw [this] at h14
      exact h14
    exact h14'
  have h15 : x = 1 := by
    have h16 : x.gcd y = 1 := hxy
    have h17 : x ∣ y := h_eq7
    have h21 : x ∣ x := by exact dvd_refl x
    have h23 : x ∣ Nat.gcd x y := by
      exact Nat.dvd_gcd h21 h17
    have h24 : Nat.gcd x y = 1 := hxy
    rw [h24] at h23
    have h25 : x = 1 := by
      have h26 : x ∣ 1 := h23
      have h27 : x ≤ 1 := by
        exact Nat.le_of_dvd (by linarith) h26
      have h28 : x > 0 := by linarith
      interval_cases x <;> try tauto
    exact h25
  rw [show x = 1 by linarith [h15] ] at h_eq5
  have h34 : y = 0 := by nlinarith
  linarith