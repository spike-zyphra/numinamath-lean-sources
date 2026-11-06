import Mathlib

theorem algebra_155546 {u : ℕ → ℝ} (hu1 : u 1 = 5)
    (hun : ∀ n ≥ 1, u (n + 1) = u n + (2 * n + 5)) :
    (∀ n ≥ 1, u n = n ^ 2 + 4 * n) ∧
    (∀ n ≥ 1, (∑ i ∈ Finset.Icc (1 : ℕ) n, (2 * i + 3 : ℝ) ^ 2) / n ≥ (n + 4) ^ 2) := by
  have goal1 : ∀ n ≥ 1, u n = n ^ 2 + 4 * n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      norm_num [hu1]
    | succ n hn ih =>
      rw [hun _ hn, ih]
      rify
      ring
  use goal1
  have h₁ (n : ℕ) (hn : n ≥ 1) : ∑ i ∈ Finset.Icc 1 n, ((2 * i + 3) : ℝ) = u n := by
    induction n, hn using Nat.le_induction with
    | base =>
      norm_num [hu1]
    | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      rify
      linear_combination -hun n hn
  intro n hn
  have h₂ := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc (1 : ℕ) n) (fun i ↦ 1) (fun i ↦ (2 * i + 3 : ℝ))
  simp [h₁ n hn, goal1 n hn] at h₂
  rw [show (n ^ 2 + 4 * n : ℝ) ^ 2 = n * ((n + 4) ^ 2 * n) by ring, mul_le_mul_left (Nat.cast_pos'.mpr hn)] at h₂
  rwa [ge_iff_le, le_div_iff₀ (Nat.cast_pos'.mpr hn)]
