import Mathlib

theorem inequalities_116047 (n : ℕ) (a : ℝ) (h₀ : 2 ≤ n) (h₁ : -1 < a) (h₂ : a ≠ 0) :
    (1 + a) ^ n > 1 + n * a := by
  have h3 : ∀ (n : ℕ), n ≥ 2 → (1 + a) ^ n > 1 + (↑n) * a := by
    intro n hn
    have base2 : (1 + a) ^ 2 > 1 + (2 : ℕ) * a := by
      norm_num
      have h4 : a ^ 2 > 0 := by
        apply sq_pos_of_ne_zero
        exact h₂
      nlinarith
    have step : ∀ (k : ℕ), k ≥ 2 → (1 + a) ^ k > 1 + (↑k) * a → (1 + a) ^ (k + 1) > 1 + (↑(k + 1)) * a := by
      intro k hk h
      have h3' : (1 + a) ^ (k + 1) = (1 + a) * ((1 + a) ^ k) := by ring
      have h4' : (1 + a) * ((1 + a) ^ k) > (1 + a) * (1 + (↑k) * a) := by
        apply mul_lt_mul_of_pos_left
        linarith [h]
        have h4 : (1 + a) > 0 := by linarith
        linarith
      have h5 : (1 + a) * (1 + (↑k) * a) = 1 + (↑(k + 1 : ℕ)) * a + (↑k : ℝ) * a ^ 2 := by
        simp [add_mul, mul_add, mul_assoc]
        ring_nf
      have h6 : (1 + a) * ((1 + a) ^ k) > (1 + (↑(k + 1 : ℕ)) * a) := by
        nlinarith [h4', h5, sq_pos_of_ne_zero (show a ≠ 0 by exact h₂), h₁, (show (k : ℝ) ≥ (2 : ℝ) by exact_mod_cast hk)]
      linarith [h3', h6]
    exact Nat.le_induction base2 step n hn
  specialize h3 n h₀
  simpa using h3