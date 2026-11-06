import Mathlib

def a (n : ℕ) := 100 + n^2
def d (n : ℕ) := Nat.gcd (a n) (a (n + 1))

theorem number_theory_283167 : IsGreatest {d n | n > 0} 401 := by
  constructor
  · -- Show 401 exists in the set
    use 200
    native_decide
  · -- Show that 401 is maximum
    intro x hx
    rcases hx with ⟨n, hn, hxn⟩
    have h1 : d n = Nat.gcd (a n) (a (n + 1)) := by simp [d, a]
    rw [h1] at hxn
    have h2 : Nat.gcd (a n) (a (n + 1)) ∣ (a n) := by
      exact Nat.gcd_dvd_left (a n) (a (n + 1))
    have h3 : Nat.gcd (a n) (a (n + 1)) ∣ (a (n + 1)) := by
      exact Nat.gcd_dvd_right (a n) (a (n + 1))
    have h4 : Nat.gcd (a n) (a (n + 1)) ∣ (a (n + 1) - a n) := by
      apply Nat.dvd_sub'
      · apply h3
      · apply h2
    have h5 : a (n + 1) - a n = 2 * n + 1 := by
      simp [a]
      <;> ring_nf <;> omega
      all_goals omega
    have h6 : Nat.gcd (a n) (a (n + 1)) ∣ (2 * n + 1) := by
      rw [h5] at h4
      exact h4
    have h7 : Nat.gcd (a n) (a (n + 1)) ∣ 401 := by
      have h11 : Nat.gcd (a n) (a (n + 1)) ∣ (100 + n^2) := by
        show Nat.gcd (a n) (a (n + 1)) ∣ a n
        apply h2
      have h12 : Nat.gcd (a n) (a (n + 1)) ∣ (2 * n + 1) := h6
      have h13 : Nat.gcd (a n) (a (n + 1)) ∣ 401 := by
        -- Compute integer combination
        have h14 : Nat.gcd (a n) (a (n + 1)) ∣ (4 * (100 + n^2) - (2 * n + 1) * (2 * n - 1)) := by
          apply Nat.dvd_sub'
          · -- Show that gcd(a_n, a_{n+1}) divides 4a_n
            apply Nat.dvd_trans h11
            norm_num
            all_goals omega
          · -- Show that gcd(a_n, a_{n+1}) divides (2n+1)(2n-1)
            apply Nat.dvd_trans h12
            apply Nat.dvd_mul_right
        have h15 : 4 * (100 + n^2) - (2 * n + 1) * (2 * n - 1) = 401 := by
          cases n with
          | zero =>
            omega  -- excluded by hn > 0
          | succ n =>
            simp [Nat.pow_succ, mul_add, mul_assoc]
            <;> ring_nf <;> omega
        rw [h15] at h14
        exact h14
      exact h13
    have h8 : Nat.gcd (a n) (a (n + 1)) ≤ 401 := by
      exact Nat.le_of_dvd (show 0 < (401 : ℕ) by linarith) h7
    linarith