import Mathlib

theorem number_theory_296611 (n : ℕ) :
    (n^2 + 100) % (n + 10) = 0 → n ≤ 190 := by
  intro h
  by_contra h1
  push_neg at h1
  have h2 : n ≥ 191 := by
    omega
  have h3 : (n + 10) ∣ (n^2 + 100) := by
    have h4 : (n ^ 2 + 100) % (n + 10) = 0 := h
    exact Nat.dvd_of_mod_eq_zero h4
  -- Now, we need to show that (n + 10) divides 200
  have h4 : (n + 10) ∣ 200 := by
    have h5 : (n + 10) ∣ (n^2 + 100) := h3
    have h6 : (n + 10) ∣ ( (n + 10) * (n - 10) ) := by
      apply dvd_mul_right
    -- Compute the difference
    have h7 : (n + 10) ∣ ( (n ^ 2 + 100) - ( (n + 10) * (n - 10) ) ) := by
      apply Nat.dvd_sub'
      · exact h5
      · exact h6
    have h8 : ( (n ^ 2 + 100) - ( (n + 10) * (n - 10) ) ) = 200 := by
      cases n with
      | zero =>
        omega
      | succ n =>
        cases n with
        | zero =>
          omega
        | succ n =>
          simp [Nat.mul_sub, Nat.sub_mul, Nat.sub_sub, Nat.add_mul, Nat.mul_add] at *
          <;> ring_nf <;> omega
    rw [h8] at h7
    exact h7
  -- n + 10 divides 200, so n + 10 ≤ 200
  have h5 : n + 10 ≤ 200 := by
    exact Nat.le_of_dvd (by norm_num) h4
  omega