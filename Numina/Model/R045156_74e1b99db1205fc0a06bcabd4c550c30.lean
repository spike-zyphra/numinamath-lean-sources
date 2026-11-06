import Mathlib

theorem number_theory_228659 (a b d : ℕ) (hd : d = Nat.gcd a b) :
    Nat.gcd (5 * a + 3 * b) (13 * a + 8 * b) = d := by 
  rw [hd]
  have h1 : Nat.gcd (5 * a + 3 * b) (13 * a + 8 * b) ∣ Nat.gcd a b := by
    -- Show that gcd(5a + 3b, 13a + 8b) divides gcd(a, b)
    have h2 : Nat.gcd (5 * a + 3 * b) (13 * a + 8 * b) ∣ (5 * a + 3 * b) := by
      exact Nat.gcd_dvd_left (5 * a + 3 * b) (13 * a + 8 * b)
    have h3 : Nat.gcd (5 * a + 3 * b) (13 * a + 8 * b) ∣ (13 * a + 8 * b) := by
      exact Nat.gcd_dvd_right (5 * a + 3 * b) (13 * a + 8 * b)
    -- Show that gcd(5a + 3b, 13a + 8b) divides a and b
    have h4 : Nat.gcd (5 * a + 3 * b) (13 * a + 8 * b) ∣ a := by
      -- From $a = 8 \cdot (5a + 3b) - 3 \cdot (13a + 8b)$
      have h5 : Nat.gcd (5 * a + 3 * b) (13 * a + 8 * b) ∣ (5 * a + 3 * b) := h2
      have h6 : Nat.gcd (5 * a + 3 * b) (13 * a + 8 * b) ∣ (13 * a + 8 * b) := h3
      have h7 : Nat.gcd (5 * a + 3 * b) (13 * a + 8 * b) ∣ (8 * (5 * a + 3 * b) - 3 * (13 * a + 8 * b)) := by
        apply Nat.dvd_sub'
        · -- Show that gcd divides 8 * (5a + 3b)
          apply Dvd.dvd.mul_left
          exact h5
        · -- Show that gcd divides 3 * (13a + 8b)
          apply Dvd.dvd.mul_left
          exact h6
      have h8 : 8 * (5 * a + 3 * b) - 3 * (13 * a + 8 * b) = a := by
        omega
      rw [h8] at h7
      exact h7
    -- Show that gcd(5a + 3b, 13a + 8b) divides b
    have h11 : Nat.gcd (5 * a + 3 * b) (13 * a + 8 * b) ∣ b := by 
      -- From $b = 5 \cdot (13a + 8b) - 13 \cdot (5a + 3b)$
      have h5 : Nat.gcd (5 * a + 3 * b) (13 * a + 8 * b) ∣ (13 * a + 8 * b) := by 
        exact Nat.gcd_dvd_right (5 * a + 3 * b) (13 * a + 8 * b)
      have h8 : Nat.gcd (5 * a + 3 * b) (13 * a + 8 * b) ∣ (5 * a + 3 * b) := by 
        exact Nat.gcd_dvd_left (5 * a + 3 * b) (13 * a + 8 * b)
      have h9 : Nat.gcd (5 * a + 3 * b) (13 * a + 8 * b) ∣ (5 * (13 * a + 8 * b) - 13 * (5 * a + 3 * b)) := by 
        apply Nat.dvd_sub'
        · -- Show that gcd divides 5 * (13a + 8b)
          apply Dvd.dvd.mul_left
          exact h5
        · -- Show that gcd divides 13 * (5a + 3b)
          apply Dvd.dvd.mul_left
          exact h8
      have h10 : 5 * (13 * a + 8 * b) - 13 * (5 * a + 3 * b) = b := by 
        omega
      rw [h10] at h9
      exact h9
    -- Since it divides both a and b, it divides gcd(a, b)
    have h12 : Nat.gcd (5 * a + 3 * b) (13 * a + 8 * b) ∣ Nat.gcd a b := by
      apply Nat.dvd_gcd h4 h11
    exact h12
  -- Show that gcd(a, b) divides gcd(5a + 3b, 13a + 8b)
  have h7 : Nat.gcd a b ∣ Nat.gcd (5 * a + 3 * b) (13 * a + 8 * b) := by
    have h2 : Nat.gcd a b ∣ (5 * a + 3 * b) := by
      have h3 : Nat.gcd a b ∣ a := by
        exact Nat.gcd_dvd_left a b
      have h4 : Nat.gcd a b ∣ b := by
        exact Nat.gcd_dvd_right a b
      have h5 : Nat.gcd a b ∣ (5 * a + 3 * b) := by
        apply Nat.dvd_add
        · -- Show that $\gcd(a, b)$ divides $5a$
          apply Dvd.dvd.mul_left
          exact h3
        · -- Show that $\gcd(a, b)$ divides $3b$
          apply Dvd.dvd.mul_left
          exact h4
      exact h5
    have h6 : Nat.gcd a b ∣ (13 * a + 8 * b) := by
      have h3 : Nat.gcd a b ∣ a := by
        exact Nat.gcd_dvd_left a b
      have h4 : Nat.gcd a b ∣ b := by
        exact Nat.gcd_dvd_right a b
      have h6 : Nat.gcd a b ∣ (13 * a + 8 * b) := by
        apply Nat.dvd_add
        · -- Show that $\gcd(a, b)$ divides $13a$
          apply Dvd.dvd.mul_left
          exact h3
        · -- Show that $\gcd(a, b)$ divides $8b$
          apply Dvd.dvd.mul_left
          exact h4
      exact h6
    -- Since it divides both, it divides the gcd
    have h7 : Nat.gcd a b ∣ Nat.gcd (5 * a + 3 * b) (13 * a + 8 * b) := by
      apply Nat.dvd_gcd h2 h6
    exact h7
  -- Since both directions, gcds are equal
  have h8 : Nat.gcd (5 * a + 3 * b) (13 * a + 8 * b) = Nat.gcd a b := by
    apply Nat.dvd_antisymm
    · exact h1
    · exact h7
  exact_mod_cast h8