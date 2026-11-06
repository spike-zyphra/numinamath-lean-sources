import Mathlib

/-The numbers in the sequence 101, 104, 109,116,… are of the form a_n=100+n^2,where n=1,2,3,… For each n, let d_n be the greatest common divisor of a_n and a_{n+1}. Find the maximum value of d_n as n ranges through the positive integers.-/
def a (n : ℕ) := 100 + n ^ 2

def d (n : ℕ) := Nat.gcd (a n) (a (n + 1))

theorem number_theory_94755 : IsGreatest {d n | n > 0} 401 := by
  constructor
  · -- Show 401 can be obtained when n = 200
    use 200
    native_decide
  · -- Show no greater value can be obtained
    intro x hx
    rcases hx with ⟨n, hn, rfl⟩
    have h1 : d n = Nat.gcd (100 + n ^ 2) (100 + (n + 1) ^ 2) := by
      simp [d, a]
    have h2 : d n = Nat.gcd (100 + n ^ 2) (2 *n +1) := by 
      rw [h1]
      have h3 : 100 + (n +1)^2 = 100 +n ^2 +2 *n +1 := by ring_nf
      rw [h3]
      have h4 : Nat.gcd (100 +n ^ 2) (100 +n ^ 2 + 2 *n +1) = 
                   Nat.gcd (100 +n ^ 2) (2 *n +1) := by 
          simp [show (100 +n ^ 2 + 2 *n +1) = (100 +n ^2) + (2 *n +1) by 
            ring_nf 
          , 
          Nat.gcd_add_mul_right_right]
      exact h4
    have h3 : d n = Nat.gcd (100 +n ^ 2) (2 *n +1) := h2
    have h4 : d n ≤ 401 := by 
      rw [h3]
      have h50 : Nat.gcd (100 +n ^ 2) (2 *n +1) ∣ 100 +n ^2 := by 
        apply Nat.gcd_dvd_left 
      have h60 : Nat.gcd (100 +n ^ 2) (2 *n +1) ∣ 2 *n +1 := by 
        apply Nat.gcd_dvd_right 
      have h70 : Nat.gcd (100 +n ^ 2) (2 *n +1) ∣ 401 := by 
        have h80 : Nat.gcd (100 +n ^ 2) (2 *n +1) ∣ (4 * (100 +n ^ 2) - (2 *n +1) * (2 *n - 1)) := by 
          apply Nat.dvd_sub' 
          · -- Show divisibility of 4*(100 +n ^ 2)
            apply Nat.dvd_trans h50 
            use 4 
            all_goals 
              ring_nf <;> omega 
          · -- Show divisibility of (2n+1)*(2n-1)
            have h34 : Nat.gcd (100 +n ^ 2) (2 *n +1) ∣ (2 *n +1) * (2 *n -1) := by 
                apply Nat.dvd_trans h60 
                use 2 *n -1 
                all_goals 
                  ring_nf <;> try omega 
            exact h34 
        have h101 : 4 * (100 +n ^2) - (2 *n +1) * (2 *n -1) = 401 := by 
          cases n with 
          | zero => 
            omega 
          | succ n => 
            simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul, mul_assoc, Nat.mul_comm]
            all_goals ring_nf 
            <;> try omega 
            <;> try tauto 
        rw [h101] at h80 
        exact h80 
      have h80 : Nat.gcd (100 +n ^ 2) (2 *n +1) ≤ 401 := by 
        exact Nat.le_of_dvd (show (401 : ℕ) > 0 by norm_num) h70 
      exact h80 
    linarith 
    all_goals norm_num 
    all_goals norm_num 
    all_goals try { tauto } 
    <;> try native_decide 
    -- Use native_decide for deep (ifier) test on larger numbers
    <;> norm_num
    <;> try { tauto } <;> norm_num <;> try omega 
    <;> try native_decide <;> norm_num 
    -- Use native_decide for deeper equality
    <;> try { trivial }
    all_goals try { native_decide }