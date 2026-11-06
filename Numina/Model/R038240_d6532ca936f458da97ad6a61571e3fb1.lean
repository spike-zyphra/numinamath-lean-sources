import Mathlib

theorem number_theory_181099 (n : ℕ) :
    5 ∣ ∑ i ∈ Finset.range 5, (n + i)^2 ∧ ¬25 ∣ ∑ i ∈ Finset.range 5, (n + i)^2 := by
  have h1 : ∑ i in Finset.range 5, (n + i)^2 = 5 * (n^2 + 4 * n + 6) := by
    simp [Finset.sum_range_succ]
    ring_nf
    <;> omega
  rw [h1]
  constructor
  · -- Show that 5 divides the sum
    use n ^ 2 + 4 * n + 6
    all_goals ring_nf
  · -- Show that 25 does not divide the sum
    intro h
    have h2 : 5 ∣ n ^ 2 + 4 * n + 6 := by
      omega
    have h3 : (n ^ 2 + 4 * n + 6) % 5 ≠ 0 := by
      have h4 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
        omega
      rcases h4 with (h4 | h4 | h4 | h4 | h4)
      · -- n % 5 = 0
        simp [Nat.add_mod, Nat.mul_mod, h4, pow_two] at *
        all_goals omega
      · -- n % 5 = 1
        simp [Nat.add_mod, Nat.mul_mod, h4, pow_two] at *
        all_goals omega
      · -- n % 5 = 2
        simp [Nat.add_mod, Nat.mul_mod, h4, pow_two] at *
        all_goals omega
      · -- n % 5 = 3
        simp [Nat.add_mod, Nat.mul_mod, h4, pow_two] at *
        all_goals omega
      · -- n % 5 = 4
        simp [Nat.add_mod, Nat.mul_mod, h4, pow_two] at *
        all_goals omega
    omega