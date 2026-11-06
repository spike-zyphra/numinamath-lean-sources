import Mathlib

/- Let $n$ be a positive integer.  How many different values can $\gcd(n + 5, n + 11)$ attain? -/
theorem number_theory_19007:
    Set.ncard {k:ℕ | ∃ (n:ℕ), k = Nat.gcd (n+11) (n+5) ∧ 0 < n} = 4 := by
  -- since gcd of n+11 and n+6 divide both, so it also divide difference of them. or say, divide (n+11)-(n+5)=6
  have h1(n:ℕ)(posn: 0 < n): Nat.gcd (n+11) (n+5) ∣ 6 := by
    have: 6 = (n+11)-(n+5) := by omega
    rw [this]
    apply Nat.dvd_sub (by simp)
    exact Nat.gcd_dvd_left (n + 11) (n + 5)
    exact Nat.gcd_dvd_right (n + 11) (n + 5)
  -- if a natural number divide 6, then it can only be 1,2,3,6.
  have h2(n:ℕ): n ∣ 6 → n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 := by
    intro h
    have: n ≤ 6 := by
      apply Nat.le_of_dvd (by norm_num) h
    interval_cases n
    any_goals simp
    <;> contradiction
  -- therefore the set is {1,2,3,6}
  have h3: {k:ℕ | ∃ (n:ℕ), k = Nat.gcd (n+11) (n+5) ∧ 0 < n}
    = {1,2,3,6} := by
    ext k; simp
    constructor <;> intro h
    · rcases h with ⟨n,hn⟩
      have hh1 := h1 n hn.right
      have hh2 := h2 (Nat.gcd (n+11) (n+5)) hh1
      rw [← hn.left] at hh2
      apply hh2
    · rcases h with k1 | k2 | k3 | k6
      · rw [k1]; use 2; simp
      · rw [k2]; use 3; simp
      · rw [k3]; use 10; simp
      · rw [k6]; use 1; simp
  -- {1,2,3,6} has 4 elements, so 4 different values.
  rw [h3]; simp [Set.ncard, Set.encard]