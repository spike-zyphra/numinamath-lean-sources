import Mathlib

theorem algebra_270227 {a : ℤ} (ha : a ≠ 1) (n : ℕ) (hn : n > 0) :
    (a ^ (n + 1) - n * (a - 1) - a) % (a - 1) ^ 2 = 0 := by
  have h1 : a - 1 ≠ 0 := by
    intro h
    apply ha
    omega
  -- need h4 second side
  have h2 : (a - 1) ^ 2 ≠ 0 := by
    apply pow_ne_zero 2
    exact h1
  have h4 : ∀ k : ℕ, (a ^ (k + 1) - k * (a - 1) - a) % (a - 1) ^ 2 = 0 := by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      have h5 : (a ^ ((k + 1 + 1 : ℕ)) - (k + 1 : ℕ) * (a - 1) - a) =
          (a ^ (k + 1 : ℕ) - (k : ℕ) * (a - 1) - a) + (a ^ (k + 1 : ℕ) * (a - 1) - (a - 1)) := by
        cases k with
        | zero =>
          norm_num
          all_goals ring
        | succ k =>
          simp [Nat.pow_succ, mul_add, mul_assoc]
          all_goals ring
      rw [h5]
      have h8 : ((a ^ (k + 1 : ℕ) * (a - 1) - (a - 1)) ) % (a - 1) ^ 2 = 0 := by
        have h9 : a ^ (k + 1 : ℕ) * (a - 1) - (a - 1) = (a - 1) * (a ^ (k + 1 : ℕ) - 1) := by ring
        rw [h9]
        have h10 : ((a - 1) * (a ^ (k + 1 : ℕ) - 1)) % (a - 1) ^ 2 = 0 := by
          have h10 : (a - 1 : ℤ) ∣ (a ^ (k + 1 : ℕ) - 1) := by
            have h7 : (a - 1 : ℤ) ∣ (a ^ (k + 1 : ℕ) - 1) := by
              apply sub_one_dvd_pow_sub_one
            exact h7
          obtain ⟨c, hc⟩ := h10
          rw [hc]
          have : ((a - 1 : ℤ) * ((a - 1) * c)) % (a - 1 : ℤ) ^ 2 = 0 := by 
            have h15 : (a - 1 : ℤ) * ((a - 1) * c) = (a - 1)^2 * c := by ring
            rw [h15]
            simp [show (a - 1 : ℤ) ^ 2 ≠ 0 by exact h2]
          assumption
        assumption
      have h11 : ( (a ^ (k + 1 : ℕ) - (k : ℕ) * (a - 1) - a) ) % (a - 1) ^ 2 = 0 := by
        exact ih
      have h12 : ( (a ^ (k + 1 : ℕ) - (k : ℕ) * (a - 1) - a) + (a ^ (k + 1 : ℕ) * (a - 1) - (a - 1)) ) % (a - 1)^2 = 0 := by
        simp [Int.add_emod, h11, h8]
      exact h12
  specialize h4 n
  simpa using h4