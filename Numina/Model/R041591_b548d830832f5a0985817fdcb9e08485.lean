import Mathlib

def sumOfGreatestComm (a b : ℕ) : ℕ := Nat.gcd a b + Nat.lcm a b

theorem number_theory_2518 (n : ℕ) : sumOfGreatestComm n (n + 1) = n * (n + 1) + 1 := by
  unfold sumOfGreatestComm
  have h1 : Nat.gcd n (n + 1) = 1 := by
    simp [Nat.gcd_comm]
    <;> try { omega }
  have h2 : Nat.lcm n (n + 1) = n * (n + 1) := by
    rw [Nat.lcm]
    rw [h1]
    all_goals 
      simp
      <;> try { ring }
      <;> try { omega }
  calc 
    Nat.gcd n (n + 1) + Nat.lcm n (n + 1)
        = 1 + (n * (n + 1)) := by
          rw [h1, h2]
    _ = n * (n + 1) + 1 := by 
      all_goals 
        ring