import Mathlib

theorem number_theory_87730 (a d : ℕ → ℕ) (ha : ∀ n, a n = 100 + n ^ 2) (hd : ∀ n, d n = Nat.gcd (a n) (a (n + 1))) : IsGreatest {d n | n > 0} 401 := by
  constructor
  · -- Show 401 is in the set
    use 200
    constructor
    · norm_num
    · -- Show that d 200 = 401
      rw [hd 200]
      rw [ha 200]
      rw [ha 201]
      norm_num [Nat.gcd]
  · -- Show no greater element is in the set
    intro x hx
    rcases hx with ⟨n, hn_pos, hn⟩
    rw [hd n] at hn
    rw [ha n] at hn
    rw [ha (n + 1)] at hn
    have h1 : Nat.gcd (100 + n ^ 2) (100 + (n + 1) ^ 2) = Nat.gcd (100 + n ^ 2) (2 * n + 1) := by
      have h2 : 100 + (n + 1) ^ 2 = (100 + n ^ 2) + (2 * n + 1) := by
        ring_nf
      rw [h2]
      simp [Nat.gcd_add_mul_right_right]
      <;> omega
    have h2 : x = Nat.gcd (100 + n ^ 2) (2 * n + 1) := by
      have h3 : Nat.gcd (100 + n ^ 2) (100 + (n + 1) ^ 2) = Nat.gcd (100 + n ^ 2) (2 * n + 1) := h1
      omega
    rw [h2]
    have h3 : Nat.gcd (100 + n ^ 2) (2 * n + 1) ∣ (100 + n ^ 2) := by
      apply Nat.gcd_dvd_left
    -- The gcd divides 2n+1
    have h4 : Nat.gcd (100 + n ^ 2) (2 * n + 1) ∣ (2 * n + 1) := by
      apply Nat.gcd_dvd_right
    -- The gcd divides 401
    have h5 : Nat.gcd (100 + n ^ 2) (2 * n + 1) ∣ 401 := by
      have h6 : Nat.gcd (100 + n ^ 2) (2 * n + 1) ∣ (100 + n ^ 2) := h3
      have h7 : Nat.gcd (100 + n ^ 2) (2 * n + 1) ∣ (2 * n + 1) := h4
      have h8 : Nat.gcd (100 + n ^ 2) (2 * n + 1) ∣ (4 * (100 + n ^ 2)) := by
        apply Dvd.dvd.mul_left
        exact h6
      have h9 : Nat.gcd (100 + n ^ 2) (2 * n + 1) ∣ ((2 * n - 1) * (2 * n + 1)) := by
        apply Dvd.dvd.mul_left
        exact h7
      have h10 : Nat.gcd (100 + n ^ 2) (2 * n + 1) ∣ (4 * (100 + n ^ 2) - (2 * n - 1) * (2 * n + 1)) := by
        apply Nat.dvd_sub'
        · -- Show that gcd (100 + n ^ 2) (2 * n + 1) ∣ 4 * (100 + n ^ 2)
          exact h8
        · -- Show that gcd (100 + n ^ 2) (2 * n + 1) ∣ (2 * n - 1) * (2 * n + 1)
          exact h9
      -- The expression 4 * (100 + n ^ 2) - (2 * n - 1) * (2 * n + 1) = 401
      have h11 : 4 * (100 + n ^ 2) - (2 * n - 1) * (2 * n + 1) = 401 := by
        cases n with
        | zero =>
          omega
        | succ n =>
          simp [Nat.pow_succ, Nat.mul_add]
          <;> ring_nf
          <;> omega
      rw [h11] at h10
      exact h10
    -- From h5: Nat.gcd (100 + n^2) (2n+1) ∣ 401. Since 401 is prime.
    have h6 : Nat.gcd (100 + n ^ 2) (2 * n + 1) ≤ 401 := by
      exact Nat.le_of_dvd (by norm_num) h5
    linarith