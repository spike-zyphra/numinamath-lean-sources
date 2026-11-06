import Mathlib

/- What is the largest integer that is a divisor of \[
(n+1)(n+3)(n+5)(n+7)(n+9)
\]for all positive even integers $n$? -/
theorem number_theory_12529 : IsGreatest {x | ∀ n : ℕ, 0 < n → Even n → x ∣ (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9)} 15 := by
  -- Two goals: show 15 satisfies the conditions and is the largest
  constructor
  . -- We show that for all positive even integers n, 15 divides (n+1)(n+3)(n+5)(n+7)(n+9)
    intro n _ _

    -- To prove 15 ∣ ?n, we need to show 3 ∣ ?n and 5 ∣ ?n respectively
    rw [show 15 = 3 * 5 by rfl]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide)

    . -- At least one of n+1, n+3, n+5, n+7, n+9 is divisible by 3
      -- It can be shown by considering the possible values of n modulo 3
      have nm3 : n % 3 < 3 := Nat.mod_lt n (by simp)
      replace nm3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      -- Case analysis on n % 3
      rcases nm3 with h | h | h

      . -- n % 3 = 0
        -- 3 ∣ n+9
        have k : 3 ∣ n + 9 := by omega
        exact Dvd.dvd.mul_left k _
      . -- n % 3 = 1
        -- 3 ∣ n+5
        have k : 3 ∣ n + 5 := by omega
        rw [show (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9) = (n + 1) * (n + 3) * (n + 7) * (n + 9) * (n + 5) by ring]
        exact Dvd.dvd.mul_left k _
      . -- n % 3 = 2
        -- 3 ∣ n+1
        have k : 3 ∣ n + 1 := by omega
        rw [show (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9) = (n + 3) * (n + 5) * (n + 7) * (n + 9) * (n + 1) by ring]
        exact Dvd.dvd.mul_left k _
    . -- At least one of n+1, n+3, n+5, n+7, n+9 is divisible by 5
      -- It can be shown by considering the possible values of n modulo 5
      have nm5 : n % 5 < 5 := Nat.mod_lt n (by simp)
      replace nm5 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
      -- Case analysis on n % 5
      rcases nm5 with h | h | h | h | h

      . -- n % 5 = 0
        -- 5 ∣ n+5
        have k : 5 ∣ n + 5 := by omega
        rw [show (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9) = (n + 1) * (n + 3) * (n + 7) * (n + 9) * (n + 5) by ring]
        exact Dvd.dvd.mul_left k _
      . -- n % 5 = 1
        -- 5 ∣ n+9
        have k : 5 ∣ n + 9 := by omega
        exact Dvd.dvd.mul_left k _
      . -- n % 5 = 2
        -- 5 ∣ n+3
        have k : 5 ∣ n + 3 := by omega
        rw [show (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9) = (n + 1) * (n + 5) * (n + 7) * (n + 9) * (n + 3) by ring]
        exact Dvd.dvd.mul_left k _
      . -- n % 5 = 3
        -- 5 ∣ n+7
        have k : 5 ∣ n + 7 := by omega
        rw [show (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9) = (n + 1) * (n + 3) * (n + 5) * (n + 9) * (n + 7) by ring]
        exact Dvd.dvd.mul_left k _
      . -- n % 5 = 4
        -- 5 ∣ n+1
        have k : 5 ∣ n + 1 := by omega
        rw [show (n + 1) * (n + 3) * (n + 5) * (n + 7) * (n + 9) = (n + 3) * (n + 5) * (n + 7) * (n + 9) * (n + 1) by ring]
        exact Dvd.dvd.mul_left k _

  . -- We show that 15 is the largest integer that satisfies the condition
    -- Suppose d is a divisor of (n+1)(n+3)(n+5)(n+7)(n+9) for all positive even integers n
    intro d hd
    simp at hd
    -- We pick n = 2, 10, 12
    have h1 := hd 2 (by simp) (by decide)
    have h2 := hd 10 (by simp) (by decide)
    have h3 := hd 12 (by simp) (by decide)
    simp at h1 h2 h3

    -- d must divide the least common multiple of the three numbers
    have h : ∀ x ∈ ([10395, 692835, 1322685] : Multiset ℕ), d ∣ x := by
      intro x
      simp
      intro hx
      obtain (rfl | rfl | rfl) := hx
      all_goals
        assumption

    -- Let Lean compute the least common multiple
    rw [← Multiset.dvd_gcd] at h
    simp [Multiset.gcd, gcd, Nat.gcd] at h

    -- d ∣ 15, so d ≤ 15
    exact Nat.le_of_dvd (by simp) h
