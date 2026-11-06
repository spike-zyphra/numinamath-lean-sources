import Mathlib

theorem number_theory_94822 : IsSquare ((Nat.factorial 17) * (Nat.factorial 18) / 2) := by
  have h1 : (Nat.factorial 18) = 18 * (Nat.factorial 17) := by
    simp [Nat.factorial]
    <;> ring
  have h2 : (Nat.factorial 17) * (Nat.factorial 18) = 18 * ((Nat.factorial 17) ^ 2) := by
    rw [h1]
    ring
  have h3 : (Nat.factorial 17) * (Nat.factorial 18) / 2 = 9 * ((Nat.factorial 17) ^ 2) := by
    rw [h2]
    norm_num
    <;> ring_nf <;> omega
  rw [h3]
  have h4 : IsSquare (9 * ((Nat.factorial 17) ^ 2)) := by
    use 3 * (Nat.factorial 17)
    all_goals ring_nf
  exact h4