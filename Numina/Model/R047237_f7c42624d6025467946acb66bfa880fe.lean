import Mathlib

theorem number_theory_275634 {n : ℕ} (hn : 2 ≤ n) :
    ∃ k d, n = k^2 + d^2 ∧ k = Nat.minFac n ∧ d ∣ n ∧ d > 1 ↔ n = 8 ∨ n = 20 := by
  by_cases h : n = 8 ∨ n = 20
  · -- Case where n = 8 or n = 20
    rcases h with (h | h)
    · -- Case n = 8
      use 2, 2
      rw [show n = 8 by omega] -- replace n with 8
      have h2 : Nat.minFac 8 = 2 := by
        norm_num [Nat.minFac]
      simp [h2]
      <;> omega
    · -- Case n = 20
      use 2, 4
      rw [show n = 20 by omega] -- replace n with 20
      have h2 : Nat.minFac 20 = 2 := by
        norm_num [Nat.minFac]
      simp [h2]
      <;> omega
  · -- Case where n ≠ 8 and n ≠ 20
    have h1 : ¬(n = 8 ∨ n = 20) := by tauto
    use 0, 0
    constructor
    · -- Assume the left side, prove the right side
      intro h
      -- left side is (n = 0^2 + 0^2 ∧ 0 = Nat.minFac n ∧ 0 ∣ n ∧ 0 > 1)
      -- right side is (n = 8 ∨ n = 20)
      -- h: n = 0^2 + 0^2 ∧ 0 = Nat.minFac n ∧ 0 ∣ n ∧ 0 > 1 
      have h4 : 0 > 1 := by 
        omega -- contradiction with h
      -- from h4 (a contradiction) we can prove anything
      exfalso 
      linarith
    · -- Assume the right side, prove the left side
      intro h
      -- right side is (n = 8 ∨ n = 20)
      -- left side is (n = 0^2 + 0^2 ∧ 0 = Nat.minFac n ∧ 0 ∣ n ∧ 0 > 1)
      -- h: n = 8 ∨ n = 20
      -- this is vacuously true since n ≠ 8 and n ≠ 20 by h1
      exfalso
      tauto