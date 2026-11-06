import Mathlib

def f (n : ℕ) := n * (n + 1) * (n + 2) * (n + 3) * (n + 4)

theorem number_theory_6399 :
    IsGreatest {k | ∀ n, 0 < n → k ∣ f n} 120 := by
  constructor
  · -- First part: Show 120 is in the set.
    show ∀ n, 0 < n → 120 ∣ f n
    intro n hn
    have h2 : 120 ∣ n * (n + 1) * (n + 2) * (n + 3) * (n + 4) := by
      have h1 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) % 3 = 0 := by
        have h1 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
        rcases h1 with (h1 | h1 | h1) <;> simp [h1, Nat.mul_mod, Nat.add_mod]
      have h2 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) % 5 = 0 := by
        have h2 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
        rcases h2 with (h2 | h2 | h2 | h2 | h2) <;> simp [h2, Nat.mul_mod, Nat.add_mod]
      have h3 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) % 8 = 0 := by
        have h3 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by omega
        rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3 | h3) <;> simp [h3, Nat.mul_mod, Nat.add_mod]
      omega
    simpa [f] using h2
  · -- Second part: Show no number greater than 120 is in the set.
    intro k hk
    have h1 : k ∣ f 1 := hk 1 (by norm_num)
    have h2 : f 1 = 120 := by
      simp [f]
      <;> omega
    rw [h2] at h1
    have h3 : k ≤ 120 := by
      exact Nat.le_of_dvd (by norm_num) h1
    linarith