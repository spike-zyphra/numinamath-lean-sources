import Mathlib

theorem number_theory_6423
    (a b : ℕ) (hab : 0 < a ∧ 0 < b) :
    Nat.gcd a b = Nat.lcm a b → a = b := by
  intro h
  have h1 : a > 0 := hab.1
  have h2 : b > 0 := hab.2
  have h3 : Nat.gcd a b * Nat.lcm a b = a * b := by 
    rw [Nat.gcd_mul_lcm]
  have h4 : Nat.gcd a b * Nat.lcm a b = a * b := h3
  have h5 : Nat.gcd a b = Nat.lcm a b := h
  have h6 : (Nat.gcd a b) ^ 2 = a * b := by
    calc
      (Nat.gcd a b) ^ 2 = Nat.gcd a b * Nat.gcd a b := by ring
      _ = Nat.gcd a b * Nat.lcm a b := by rw [h5]
      _ = a * b := by rw [h4]
  have h7 : Nat.gcd a b ∣ a := by 
    exact Nat.gcd_dvd_left a b
  have h8 : Nat.gcd a b ∣ b := by 
    exact Nat.gcd_dvd_right a b
  rcases h7 with ⟨m, hm⟩
  rcases h8 with ⟨n, hn⟩
  have h7' : (Nat.gcd a b) ^ 2 = (Nat.gcd a b) ^ 2 * (m * n) := by
    have eq1 : (Nat.gcd a b) ^ 2 = a * b := h6
    rw [show a = Nat.gcd a b * m by linarith [hm], 
        show b = Nat.gcd a b * n by linarith [hn]] at eq1
    nlinarith [eq1]
  -- From Nat.gcd a b > 0 and (Nat.gcd a b) ^ 2 = (Nat.gcd a b) ^ 2 * (m * n) to m * n = 1 
  have h12 : m * n = 1 := by
    have h13 : (Nat.gcd a b) ^ 2 > 0 := by
      have h14 : Nat.gcd a b > 0 := by
        apply Nat.gcd_pos_of_pos_left
        linarith
      have : (Nat.gcd a b) ^ 2 > 0 := by
        nlinarith
      linarith
    have h14 : (m * n) = 1 := by
      nlinarith [h7']
    exact_mod_cast h14
  -- m and n must be 1 since they multiply to 1 (m*n=1).
  have h13 : m = 1 := by
    have h14 : m ∣ 1 := by
      use n
      all_goals linarith
    have h15 : m = 1 := by
      exact Nat.eq_one_of_dvd_one h14
    exact h15
  have h14 : n = 1 := by
    have h15 : n ∣ 1 := by
      use m
      all_goals linarith
    have h16 : n = 1 := by
      exact Nat.eq_one_of_dvd_one h15
    exact h16
  -- Substitute back into the expressions for a and b.
  have h15 : a = Nat.gcd a b := by 
    nlinarith [hm, h13]
  have h16 : b = Nat.gcd a b := by 
    nlinarith [hn, h14]
  -- Therefore, a = b since both equal to Nat.gcd a b
  linarith [h15, h16]