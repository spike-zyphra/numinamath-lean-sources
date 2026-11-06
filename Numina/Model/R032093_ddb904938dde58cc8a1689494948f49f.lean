import Mathlib

theorem number_theory_128479 :
    IsGreatest {x | ∃ a b, x = Nat.gcd a b ∧ a * b = 600000} 200 := by
  constructor
  · -- Show 200 is in the set by using the pair (600, 1000).
    use 600, 1000
    all_goals norm_num
  · -- Show that max possible GCD is 200.
    intro x hx
    rcases hx with ⟨a, b, h_eq, h_prod⟩
    -- Let $g = Nat.gcd \ a \ b$. Let's use $g \cdot g$ divides $a \cdot b$.
    -- Let's get g^2 | (a*b).
    have h1 : x = Nat.gcd a b := by
      exact h_eq
    have h2 : Nat.gcd a b ∣ a := by
      exact Nat.gcd_dvd_left a b
    have h3 : Nat.gcd a b ∣ b := by
      exact Nat.gcd_dvd_right a b
    have h4 : (Nat.gcd a b) ^ 2 ∣ (a * b) := by
      have h5 : Nat.gcd a b ∣ a := h2
      have h6 : Nat.gcd a b ∣ b := h3
      have h7 : (Nat.gcd a b) * (Nat.gcd a b) ∣ a * b := by
        apply Nat.mul_dvd_mul
        exact h5
        exact h6
      have h8 : (Nat.gcd a b) * (Nat.gcd a b) = (Nat.gcd a b) ^ 2 := by ring
      rw [h8] at h7
      exact h7
    have h9 : (Nat.gcd a b) ^ 2 ∣ 600000 := by
      have h10 : a * b = 600000 := h_prod
      rw [h10] at h4
      exact h4
    have h10 : Nat.gcd a b ≤ 774 := by
      by_contra h
      push_neg at h
      have h11 : Nat.gcd a b > 774 := by linarith
      have h12 : Nat.gcd a b ≥ 775 := by omega
      have h13 : (Nat.gcd a b) ^ 2 ≥ 600625 := by
        have h14 : Nat.gcd a b ≥ 775 := by omega
        have h15 : (Nat.gcd a b) ^ 2 ≥ 775 ^ 2 := by
          have h16 : Nat.gcd a b ≥ 775 := h14
          have : (Nat.gcd a b) ^ 2 ≥ (775) ^ 2 := by
            apply Nat.pow_le_pow_of_le_left
            exact h16
          exact_mod_cast this
        norm_num at h15 ⊢
        all_goals linarith
      have h14 : (Nat.gcd a b) ^ 2 ≤ 600000 := by
        exact Nat.le_of_dvd (by norm_num) h9
      nlinarith
    by_contra h
    push_neg at h
    have h11 : Nat.gcd a b > 200 := by linarith
    have h12 : Nat.gcd a b ≥ 201 := by omega
    have h13 : (Nat.gcd a b) ^ 2 ∣ 600000 := h9
    -- now if `Nat.gcd a b` is between 201 and 774, we get a contradiction
    -- we now work on contradiction
    have h14 : Nat.gcd a b ≤ 774 := h10
    interval_cases h17 : Nat.gcd a b <;> try { 
      omega 
    } <;> try { 
      norm_num at h13 h14 ⊢ 
      all_goals omega 
    }