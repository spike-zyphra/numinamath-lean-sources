import Mathlib

open Real
open scoped BigOperators

theorem algebra_280821 {f : ℕ → ℝ} (hf : ∀ n, f n = 100 ^ n / Nat.factorial n) :
    ∃ n, ∀ m > n, f m < f n := by

  use 100

  intro m h3

  have h1 : f m = (100 : ℝ) ^ m / Nat.factorial m := hf m
  have h2 : f 100 = (100 : ℝ) ^ 100 / Nat.factorial 100 := hf 100

  rw [h1, h2]

  have h5 : ∀ m : ℕ, m > 100 → ((100 : ℝ) ^ m / Nat.factorial m) < (100 : ℝ) ^ 100 / Nat.factorial 100 := by
    intro m h
    induction m with
    | zero => 
      linarith
    | succ m ih =>
      by_cases h' : m > 100
      · -- Case where m > 100
        have h6 : ((100 : ℝ) ^ (m + 1) / Nat.factorial (m + 1)) =
          ((100 : ℝ) ^ m / Nat.factorial m) * (100 / ((m : ℝ) + 1)) := by
          field_simp [Nat.factorial]
          <;> ring_nf <;> simp
          <;> ring_nf <;> norm_num
        rw [h6]
        have h7 : ((100 : ℝ) ^ m / Nat.factorial m) > 0 := by
          positivity
        have h8 : (100 : ℝ) / ((m : ℝ) + 1) > 0 := by
          positivity
        have h9 : ((100 : ℝ) ^ 100 / Nat.factorial 100) > 0 := by
          positivity
        have h10 : ((100 : ℝ) ^ m / Nat.factorial m) < (100 : ℝ) ^ 100 / Nat.factorial 100 := ih h'
        have h11 : (100 : ℝ) / ((m : ℝ) + 1) < 1 := by
          have h4 : (m : ℝ) + 1 > (100 : ℝ) := by
            have h5 : m > 100 := h'
            have h6 : (m : ℝ) > (100 : ℝ) := by exact_mod_cast h5
            linarith
          have h7 : (m : ℝ) + 1 > (0 : ℝ) := by
            nlinarith
          have h8 : (100 : ℝ) > 0 := by norm_num
          apply (div_lt_iff (by positivity)).mpr
          nlinarith
        have h12 : ((100 : ℝ) ^ m / Nat.factorial m) * (100 / ((m : ℝ) + 1)) < ((100 : ℝ) ^ 100 / Nat.factorial 100) := by
          have h13 : ((100 : ℝ) ^ m / Nat.factorial m) * (100 / ((m : ℝ) + 1)) < ((100 : ℝ) ^ 100 / Nat.factorial 100) := by
            have h7 : (100 / ((m : ℝ) + 1)) > 0 := by positivity
            have h8 : ((100 : ℝ) ^ m / Nat.factorial m) < (100 : ℝ) ^ 100 / Nat.factorial 100 := h10
            have h12 : (100 / ((m : ℝ) + 1)) < 1 := h11
            nlinarith [h8, h12, mul_pos (show 0 < ((100 : ℝ) ^ 100 / Nat.factorial 100) by positivity) (show 0 < (100 : ℝ) / ((m : ℝ) + 1) by positivity)]
          linarith
        linarith
      · -- Case where m <= 100, so m + 1 = 101
        have h13 : m = 100 := by omega
        rw [h13]
        norm_num [Nat.factorial]
        <;> norm_num
        <;> native_decide

  have h4 : m > 100 := h3
  specialize h5 m h4
  linarith [h5]