import Mathlib

open Finset Real Nat

theorem algebra_11123 {a : ℕ → ℝ}
    (ha1 : a 1 = 1)
    (han : ∀ n ≥ 2, a n = n / (n ^ 2 - 1)) :
    ∀ n ≥ 1, ∑ k ∈ Icc 1 n, (∏ i ∈ Icc 1 k, a i) = 2 - 2 / (n + 1).factorial := by
  intro n hn
  have h1 : ∀ k : ℕ, k ≥ 1 → (∏ i ∈ Icc 1 k, a i) = 2 * k / ((k + 1).factorial : ℝ) := by
    intro k hk
    induction k with
    | zero =>
      exfalso
      linarith
    | succ k ih =>
      cases k with
      | zero =>
        simp [ha1]
        all_goals norm_num
        all_goals linarith
      | succ k =>
        rw [prod_Icc_succ_top (by linarith)]
        rw [ih (by linarith)]
        have hk2 : k + 2 ≥ 2 := by
          linarith
        have ha2 : a (k + 2 : ℕ) = ((k + 2 : ℕ) : ℝ) / ((k + 2 : ℕ) ^ 2 - 1) := by
          apply han
          all_goals omega
        simp [ha2]
        field_simp [Nat.factorial]
        <;> ring_nf <;> field_simp [Nat.factorial] <;> ring
  have h2 : ∀ n : ℕ, n ≥ 1 → ∑ k ∈ Icc 1 n, (∏ i ∈ Icc 1 k, a i) = 2 - 2 / (n + 1).factorial := by
    intro n hn
    induction n with
    | zero =>
      exfalso
      linarith
    | succ n ih =>
      cases n with
      | zero =>
        norm_num [h1, ha1]
        all_goals norm_num [Nat.factorial]
      | succ n =>
        rw [sum_Icc_succ_top (by linarith)]
        rw [h1 (n + 2) (by linarith)]
        rw [ih (by linarith)]
        field_simp [Nat.factorial]
        <;> ring_nf <;> field_simp [Nat.factorial] <;> ring
  specialize h2 n hn
  simpa using h2