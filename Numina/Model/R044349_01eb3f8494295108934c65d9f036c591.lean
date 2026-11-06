import Mathlib

theorem algebra_250739 (x : ℕ) : 4 ^ x + 9 ^ x = 2 * 6 ^ x ↔ x = 0:= by
  constructor
  · -- Forward direction: if 4^x + 9^x = 2 * 6^x then x = 0.
    intro h_eq
    have eq1 : (4 : ℕ) ^ x + (9 : ℕ) ^ x = 2 * (6 : ℕ) ^ x := by
      exact_mod_cast h_eq
    have h1 : x = 0 := by
      have eq3 : (2 ^ x : ℕ) ^ 2 + (3 ^ x : ℕ) ^ 2 = 2 * ((2 ^ x : ℕ) * (3 ^ x : ℕ)) := by
        have eq4 : (4 : ℕ) ^ x = (2 ^ x : ℕ) ^ 2 := by
          have h1 : ∀ (x : ℕ), (4 : ℕ) ^ x = (2 : ℕ) ^ (2 * x) := by
            intro x
            rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
            rw [← pow_mul]
            all_goals omega
          rw [h1 x]
          have h2 : (2 : ℕ) ^ (2 * x) = ((2 : ℕ) ^ x) ^ 2 := by
            ring_nf
          rw [h2]
        have eq5 : (9 : ℕ) ^ x = (3 ^ x : ℕ) ^ 2 := by
          have h1 : ∀ (x : ℕ), (9 : ℕ) ^ x = (3 : ℕ) ^ (2 * x) := by
            intro x
            rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
            rw [← pow_mul]
            all_goals omega
          rw [h1 x]
          have h2 : (3 : ℕ) ^ (2 * x) = ((3 : ℕ) ^ x) ^ 2 := by
            ring_nf
          rw [h2]
        have eq6 : (6 : ℕ) ^ x = (2 ^ x : ℕ) * (3 ^ x : ℕ) := by
          have h1 : ∀ (x : ℕ), (6 : ℕ) ^ x = (2 * 3) ^ x := by
            intro x
            rw [show (6 : ℕ) = 2 * 3 by norm_num]
          rw [h1 x]
          rw [mul_pow]
        rw [eq4, eq5, eq6] at eq1
        ring_nf at eq1 ⊢
        omega
      have eq4 : (2 ^ x : ℕ) = (3 ^ x : ℕ) := by
        nlinarith
      have eq5 : x = 0 := by
        have eq6 : (2 : ℕ) ^ x = (3 : ℕ) ^ x := eq4
        have eq7 : ∀ (x : ℕ), (2 : ℕ) ^ x = (3 : ℕ) ^ x → x = 0 := by
          intro x heq
          have h12 : (2 : ℕ) ^ x = (3 : ℕ) ^ x := heq
          have base0 : x = 0 := by
            by_cases h2 : x > 0
            · -- Assume x > 0
              have eq5 : (2 : ℕ) ^ x < (3 : ℕ) ^ x := by
                apply Nat.pow_lt_pow_left
                all_goals omega
              linarith [eq5, h12]
            · -- x = 0
              omega
          exact_mod_cast base0
        apply eq7 x eq6
      exact_mod_cast eq5
    exact_mod_cast h1
  · -- Backward direction: if x = 0, then 4^x + 9^x = 2 * 6^x.
    intro h_eq
    rw [h_eq]
    all_goals norm_num