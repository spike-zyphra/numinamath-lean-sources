import Mathlib

theorem number_theory_6728 {n : ℕ} (hn : Even n) :
    Nat.lcm n (n + 2) = 10 * (n + 2) ↔ (n + 2)^2 - n^2 = 84 := by
  have h1 : (n + 2) ^ 2 - n ^ 2 = 4 * n + 4 := by
    cases n with
    | zero =>
      all_goals omega
    | succ n =>
      cases n with
      | zero =>
        all_goals omega
      | succ n =>
        simp [Nat.pow_two, Nat.mul_add, Nat.add_mul]
        <;> ring_nf <;> omega
  -- Prove that (n+2)^2 - n^2 = 84 ↔ n=20
  have h2 : (n + 2)^2 - n^2 = 84 ↔ n = 20 := by
    constructor
    · -- Assume (n + 2)^2 - n^2 = 84, prove n = 20
      intro h
      have h3 : 4 * n + 4 = 84 := by
        omega -- uses h1 and h.
      omega -- Solves 4n+4=84 to n=20
    · -- Assume n = 20, prove (n + 2)^2 - n^2 = 84
      intro h
      subst n
      all_goals omega
  -- Now, we need to prove the theorem using the property from h2.
  rw [show (n + 2) ^ 2 - n ^ 2 = 84 ↔ n = 20 by tauto]
  constructor
  · -- Forward direction: Assume Nat.lcm n (n + 2) = 10 * (n + 2), prove n = 20
    intro h
    have h7 : n % 2 = 0 := by
      obtain ⟨k, hk⟩ := hn
      omega
    by_cases h8 : n > 0
    · -- Case n > 0
      have h9 : n % 2 = 0 := h7
      have h20 : n.gcd (n + 2) = 2 := by 
        have h18 : n.gcd (n + 2) ∣ 2 := by
          have h19 : n.gcd (n + 2) ∣ n := by
            apply Nat.gcd_dvd_left
          have h20 : n.gcd (n + 2) ∣ (n + 2) := by
            apply Nat.gcd_dvd_right
          have h21 : n.gcd (n + 2) ∣ ((n + 2) - n) := by
            apply Nat.dvd_sub' 
            · exact h20
            · exact h19
          have h22 : ((n + 2 : ℕ) - n) = 2 := by
            omega
          rw [h22] at h21
          exact h21
        have h22 : 2 ∣ n.gcd (n + 2) := by
          have h23 : 2 ∣ n := by 
            omega
          have h24 : 2 ∣ (n + 2) := by 
            omega
          have h26 : 2 ∣ n.gcd (n + 2) := by 
            exact Nat.dvd_gcd h23 h24
          exact h26
        have h24 : n.gcd (n + 2) ∣ 2 := h18
        have h25 : n.gcd (n + 2) ≥ 2 := by 
          by_contra h'
          push_neg at h'
          have h26 : n.gcd (n + 2) < 2 := by omega
          have h27 : n.gcd (n + 2) = 0 ∨ n.gcd (n + 2) = 1 := by 
            interval_cases (n.gcd (n + 2)) <;> tauto
          cases h27 with
          | inl h0 =>
            have h00 : n.gcd (n + 2) = 0 := h0
            have h01 : n.gcd (n + 2) > 0 := by 
              apply Nat.gcd_pos_of_pos_left
              omega
            omega
          | inr h1 =>
            have h11 : n.gcd (n + 2) = 1 := h1
            omega
        have h14 : n.gcd (n + 2) ≤ 2 := by 
          exact Nat.le_of_dvd (by omega) h24
        interval_cases (n.gcd (n + 2)) <;> omega
      have eq1 : n * (n + 2) = n.gcd (n + 2) * (n.lcm (n + 2)) := by
        rw [Nat.gcd_mul_lcm]
      have h111 : n * (n + 2) = 20 * (n + 2) := by
        have h99 : n.gcd (n + 2) = 2 := h20
        have h98 : n.lcm (n + 2) = 10 * (n + 2) := h
        rw [h99, h98] at eq1
        nlinarith
      have h112 : n = 20 := by
        nlinarith
      linarith
    · -- Case n ≤ 0, so n = 0.
      have h0 : n = 0 := by
        omega
      subst n 
      simp [Nat.lcm] at h 
      all_goals omega
  · -- Backward direction: Assume n = 20, prove Nat.lcm n (n + 2) = 10 * (n + 2)
    intro h
    subst n
    all_goals norm_num [Nat.lcm]