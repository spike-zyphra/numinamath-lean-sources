import Mathlib

theorem algebra_13504 {a : ℕ → ℤ} (ha : a 1 = 10) (h : ∀ m > 0, a (m + 1) = a m + 3 * a 1) :
    a 2022 = 60640 := by
  -- Show by induction that for all n, a (n + 1) = 10 + n * 30
  have ha_n : ∀ n, a (n + 1) = 10 + (n : ℕ) * 30 := by
    intro n
    induction n with
    | zero =>
      -- Base case: n = 0, so show a(1) = 10
      simp [ha]
      all_goals omega
    | succ k ih =>
      -- Induction step: assume it holds for k, prove for k + 1
      calc
        a ((k + 1) + 1) = a (k + 1) + 30 := by
          have h2 := h (k + 1) (by linarith)
          rw [h2]
          have ha1 : a 1 = 10 := ha
          rw [ha1]
          all_goals omega
        _ = (10 + (k : ℕ) * 30) + 30 := by rw [ih]
        _ = 10 + ((k + 1 : ℕ) ) * 30 := by
          simp [Nat.add_comm, Nat.mul_add]
          all_goals omega
  -- Now apply the formula to n = 2021 to get a(2022)
  have h2022 := ha_n 2021
  norm_num at h2022 ⊢
  exact h2022