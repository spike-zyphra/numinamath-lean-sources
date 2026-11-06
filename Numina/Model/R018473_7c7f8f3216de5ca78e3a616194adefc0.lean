import Mathlib

theorem algebra_11954 {n : ℕ} (hn : n > 0) (h : (n ^ 2 + 9 * n - 2) % (11 + n) = 0) :
    n = 9 := by
  have h1 : (11 + n) ∣ (n ^ 2 + 9 * n - 2) := by
    exact Nat.dvd_of_mod_eq_zero h

  have h2 : (11 + n) ∣ 20 := by
    have h3 : (11 + n) ∣ (n ^ 2 + 9 * n - 2) := h1
    have h4 : (11 + n) ∣ (n + 11) * (n - 2) := by
      use n - 2
      <;> ring_nf
      <;> omega
    have h5 : (11 + n) ∣ ((n ^ 2 + 9 * n - 2) - ((n + 11) * (n - 2))) := by
      apply Nat.dvd_sub'
      · exact h3
      · exact h4
    have eq1 : ((n ^ 2 + 9 * n - 2) - ((n + 11) * (n - 2))) = 20 := by
      cases n with
      | zero =>
        all_goals omega
      | succ n =>
        cases n with
        | zero =>
          all_goals omega
        | succ n =>
          cases n with
          | zero =>
            all_goals omega
          | succ n =>
            simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, mul_assoc]
            <;> ring_nf
            <;> omega
    rw [eq1] at h5
    exact h5

  have h3 : (11 + n) ≤ 20 := by
    exact Nat.le_of_dvd (by omega) h2

  have h4 : n ≤ 9 := by
    omega

  interval_cases n <;> try { 
    norm_num at h1 
    all_goals omega 
  }
  <;> norm_num at h2 
  <;> norm_num at h 
  <;> omega