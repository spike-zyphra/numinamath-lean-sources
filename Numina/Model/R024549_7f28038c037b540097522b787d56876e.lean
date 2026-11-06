import Mathlib


theorem number_theory_228318 {n : ℕ} (hn : n ≥ 3) (m : ℕ) (hm : m = n * (n - 1) / 2)
    (h : ∀ i j, i ≠ j → (i + 1 + j + 1) % m ≠ (i + 1 + i + 1) % m) :
    Odd m → ∃ k, k^2 = n - 2 := by
  intro h_odd
  have h4 : m > 0 := by
    rw [hm]
    have h10 : n ≥ 3 := hn
    have h11 : n * (n - 1) / 2 > 0 := by
      have h13 : n * (n - 1) ≥ 6 := by
        have h14 : n ≥ 3 := hn
        have h15 : n - 1 ≥ 2 := by
          omega
        have h16 : n * (n - 1) ≥ 3 * 2 := by
          nlinarith [show n ≥ 3 by linarith, show n - 1 ≥ 2 by omega]
        omega
      have h17 : n * (n - 1) ≥ 6 := h13
      have h18 : n * (n - 1) / 2 > 0 := by
        omega
      exact h18
    omega

  have h3 := h 0 m (by
    have : 0 ≠ m := by
      omega
    tauto
  )
  have h5 : (0 + 1 + m + 1) % m = (0 + 1 + 0 + 1) % m := by
    have h7 : (0 + 1 + m + 1 : ℕ) % m = (0 + 1 + 0 + 1 : ℕ) % m := by
      have h10 : (0 + 1 + m + 1 : ℕ) % m = 2 % m := by
        have h11 : (0 + 1 + m + 1 : ℕ) = m + 2 := by
          omega
        rw [h11]
        simp [Nat.add_mod]
      have h10' : (0 + 1 + 0 + 1 : ℕ) % m = 2 % m := by
        have h11' : (0 + 1 + 0 + 1 : ℕ) = 2 := by
          omega
        rw [h11']
      omega
    omega
  exfalso
  tauto