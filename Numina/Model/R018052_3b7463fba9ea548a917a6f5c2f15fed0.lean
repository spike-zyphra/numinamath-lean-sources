import Mathlib

theorem number_theory_192672 :
    IsGreatest {x | ∃ m n, x = Nat.gcd (m + 2000 * n) (n + 2000 * m) ∧ Nat.gcd m n = 1} 3999999 := by
  constructor
  · -- Show that 3999999 is in the set
    use 1, 3997999
    all_goals norm_num
  · -- Show that any element in the set is ≤ 3999999
    intro x hx
    rcases hx with ⟨m, n, hx, h1⟩
    rw [hx] at *
    have h2 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ (m + 2000 * n) := by apply Nat.gcd_dvd_left
    have h3 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ (n + 2000 * m) := by apply Nat.gcd_dvd_right
    have h4 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ (3999999 * m) := by
      have h5 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ (2000 * (n + 2000 * m) - (m + 2000 * n)) := by
        apply Nat.dvd_sub'
        · -- Show that $d$ divides $2000 \cdot (n + 2000m)$
          apply Dvd.dvd.mul_left
          exact h3
        · -- Show that $d$ divides $m + 2000n$
          exact h2
      have h6 : (2000 * (n + 2000 * m) - (m + 2000 * n)) = 3999999 * m := by
        omega
      rw [h6] at h5
      exact h5
    have h8 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ (3999999 * n) := by
      have h9 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ (2000 * (m + 2000 * n) - (n + 2000 * m)) := by
        apply Nat.dvd_sub'
        · -- Show that $d$ divides $2000 \cdot (m + 2000n)$
          apply Dvd.dvd.mul_left
          exact h2
        · -- Show that $d$ divides $n + 2000m$
          exact h3
      have h10 : (2000 * (m + 2000 * n) - (n + 2000 * m) ) = 3999999 * n := by
        omega
      rw [h10] at h9
      exact h9
    have h12 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ 3999999 := by
      have h13 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ Nat.gcd (3999999 * m) (3999999 * n) := by
        apply Nat.dvd_gcd
        · exact h4
        · exact h8
      have h14 : Nat.gcd (3999999 * m) (3999999 * n) = 3999999 * (Nat.gcd m n) := by
        rw [show 3999999 * m = 3999999 * m by rfl, show 3999999 * n = 3999999 * n by rfl]
        rw [Nat.gcd_mul_left]
      rw [h14] at h13
      rw [h1] at h13
      have h15 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ∣ 3999999 := by
        exact h13
      exact h15
    have h15 : Nat.gcd (m + 2000 * n) (n + 2000 * m) ≤ 3999999 := by
      exact Nat.le_of_dvd (by omega) h12
    linarith