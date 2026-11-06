import Mathlib

theorem number_theory_116820 {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : Nat.gcd a b = 20) (h2 : Nat.lcm a b = 100) :
    (Nat.gcd (10 * a) (10 * b) = 20 * 10) ∧
    (Nat.lcm (10 * a) (10 * b) = 100 * 10) ∧
    (Nat.gcd a b * 100 = 20 * 100) := by 
  constructor
  · -- Prove that gcd (10 * a) (10 * b) = 200
    have h3 : Nat.gcd (10 * a) (10 * b) = 10 * (Nat.gcd a b) := by
      simp [Nat.gcd_mul_left]
      all_goals try linarith
    rw [h3, h1]
    all_goals try omega
  constructor
  · -- Prove that lcm (10 * a) (10 * b) = 1000
    have h3 : Nat.gcd (10 * a) (10 * b) = 10 * (Nat.gcd a b) := by
      simp [Nat.gcd_mul_left]
      all_goals try linarith
    have h4 : Nat.gcd (10 * a) (10 * b) = 200 := by
      rw [h3, h1]
      all_goals try linarith
    have h5 : Nat.lcm (10 * a) (10 * b) = 1000 := by
      have h6 : a * b = 2000 := by 
        have h8 : a.gcd b * a.lcm b = a * b := by 
          rw [Nat.gcd_mul_lcm]
          <;> try tauto <;> try nlinarith <;> try tauto
        rw [h1, h2] at h8
        omega
      have h7 : (10 * a).lcm (10 * b) = (10 * a * (10 * b)) / (Nat.gcd (10 * a) (10 * b)) := by 
        rw [Nat.lcm]
        <;> try simp [Nat.mul_assoc] 
        <;> try tauto
      rw [h7]
      rw [h4]
      have h9 : a * b = 2000 := h6
      have h10 : (10 * a * (10 * b)) = 100 * (a * b) := by 
        ring_nf 
        <;> omega 
      rw [h10, h9]
      all_goals norm_num 
      <;> try omega 
      all_goals try tauto 
    exact_mod_cast h5 
  · -- Prove that the product of a and b is 2000
    calc 
      Nat.gcd a b * 100 = 20 * 100 := by 
        rw [h1]
        <;> omega 
      _ = 20 * 100 := by 
        all_goals try omega