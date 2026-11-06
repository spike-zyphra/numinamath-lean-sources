import Mathlib

theorem number_theory_240725 (a b : ℕ) :
    ¬(2 ∣ a) ∧ ¬(3 ∣ a) ∧ ¬(2 ∣ b) ∧ ¬(3 ∣ b) →
    ∃ n, a * b = 6 * n + 1 ∨ a * b = 6 * n + 5 := by
  intro h
  have ha1 : a % 6 = 1 ∨ a % 6 = 5 := by
    omega
  have hb1 : b % 6 = 1 ∨ b % 6 = 5 := by
    omega
  rcases ha1 with (ha1 | ha1) <;> rcases hb1 with (hb1 | hb1)
  · -- Case a % 6 = 1 and b % 6 = 1
    use (a * b - 1) / 6
    left
    have h1 : (a * b) % 6 = 1 := by
      simp [Nat.mul_mod, ha1, hb1]
      all_goals omega
    have h2 : a * b = 6 * ((a * b - 1) / 6) + 1 := by
      omega
    linarith
  · -- Case a % 6 = 1 and b % 6 = 5
    use (a * b - 5) / 6
    right
    have h1 : (a * b) % 6 = 5 := by
      simp [Nat.mul_mod, ha1, hb1]
      all_goals omega
    have h2 : a * b = 6 * ((a * b - 5) / 6) + 5 := by
      omega
    linarith
  · -- Case a % 6 = 5 and b % 6 = 1
    use (a * b - 5) / 6
    right
    have h1 : (a * b) % 6 = 5 := by
      simp [Nat.mul_mod, ha1, hb1]
      all_goals omega
    have h2 : a * b = 6 * ((a * b - 5) / 6) + 5 := by
      omega
    linarith
  · -- Case a % 6 = 5 and b % 6 = 5
    use (a * b - 1) / 6
    left
    have h1 : (a * b) % 6 = 1 := by
      simp [Nat.mul_mod, ha1, hb1]
      all_goals omega
    have h2 : a * b = 6 * ((a * b - 1) / 6) + 1 := by
      omega
    linarith