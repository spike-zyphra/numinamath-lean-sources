import Mathlib

open Real

theorem inequalities_597464 (x : ℝ) (hx : -1 < x) (hx1 : x ≠ 0)
    (n : ℕ) (hn : 2 ≤ n) : (1 + x) ^ n > 1 + n * x := by
  have h1 : x > -1 := hx
  have h2 : x ≠ 0 := hx1
  have h3 : ∀ n : ℕ, n ≥ 2 → (1 + x) ^ n > 1 + ↑n * x := by
    intro n hn
    have h4 : n ≥ 2 := hn
    have base2 : (1 + x) ^ 2 > 1 + (2 : ℝ) * x := by
      have h8 : x ^ 2 > (0 : ℝ) := by
        apply pow_two_pos_of_ne_zero
        exact h2
      nlinarith
    have step : ∀ (k : ℕ), k ≥ 2 → (1 + x) ^ k > 1 + ↑k * x → (1 + x) ^ (k + 1) > 1 + ↑(k + 1 : ℕ) * x := by
      intro k hk h
      have h4 : k ≥ 2 := hk
      have h6 : (1 + x) ^ (k + 1 : ℕ) = ( (1 + x) ^ k ) * (1 + x) := by
        ring_nf
      have h7 : (1 + x) ^ k > 1 + ↑k * x := h
      have h8 : (1 + x) > 0 := by
        linarith
      have h9 : (1 + x) ^ (k + 1 : ℕ) = ( (1 + x) ^ k ) * (1 + x) := by
        ring_nf
      have h10 : ( (1 + x) ^ k ) * (1 + x) > (1 + ↑k * x) * (1 + x) := by
        apply mul_lt_mul_of_pos_right h7 h8
      have h15 : (1 + ↑k * x) * (1 + x) ≥ (1 + ↑(k + 1 : ℕ) * x) := by
        have eq : (1 + ↑k * x) * (1 + x) = 1 + ↑(k + 1 : ℕ) * x + (↑k * x ^ 2 : ℝ) := by
          simp [mul_add, add_mul]
          <;> ring_nf <;> simp [mul_add, add_mul]
          <;> ring
        rw [eq]
        have h2_pos : x ^ 2 ≥ 0 := by exact sq_nonneg x
        have hk_cast_nonneg : (↑k : ℝ) ≥ 0 := by
          have hk_nat_nonneg : k ≥ 0 := by omega
          exact_mod_cast hk_nat_nonneg
        have hk_mul_nonneg : (↑k : ℝ) * x ^ 2 ≥ 0 := by
          apply mul_nonneg hk_cast_nonneg h2_pos
        linarith
      have h11 : ( (1 + x) ^ k ) * (1 + x) > (1 + ↑(k + 1 : ℕ) * x) := by
        linarith [h10, h15]
      rw [h6]
      linarith [h11]
    exact Nat.le_induction base2 step n h4
  specialize h3 n hn
  simpa using h3