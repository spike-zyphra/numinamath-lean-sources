import Mathlib

open BigOperators

theorem other_294337 (A B : ℝ) (hA : 1 < A) (hB : 1 < B)
    (a : ℕ → ℝ) (ha : ∀ n, 1 ≤ a n ∧ a n ≤ A * B) :
    ∃ b : ℕ → ℝ, (∀ n, 1 ≤ b n ∧ b n ≤ A) ∧
    (∀ m n, a m / a n ≤ B * b m / b n) := by
  use (fun n => min (a n) A)
  constructor
  · -- Show that for all n, 1 ≤ b n ∧ b n ≤ A
    intro n
    constructor
    · -- Show 1 ≤ b n
      have h1 : 1 ≤ a n := (ha n).1
      have h2 : 1 ≤ min (a n) A := by
        cases min_cases (a n) A with
        | inl h =>
          linarith
        | inr h =>
          nlinarith
      linarith
    · -- Show b n ≤ A
      have h3 : min (a n) A ≤ A := by
        cases min_cases (a n) A with
        | inl h =>
          nlinarith
        | inr h =>
          nlinarith
      linarith
  · -- Show that for all m, n, a m / a n ≤ B * b m / b n
    intro m n
    have h1 : 1 ≤ a m := (ha m).1
    have h2 : 1 ≤ a n := (ha n).1
    have h3 : a m ≤ A * B := (ha m).2
    have h4 : a n ≤ A * B := (ha n).2
    have h5 : a m * (min (a n) A) ≤ B * (a n * (min (a m) A)) := by
      by_cases h7 : a n ≤ A
      · -- If a_n ≤ A, then min (a n) A = a n
        rw [min_eq_left (show a n ≤ A by linarith)]
        by_cases h8 : a m ≤ A
        · -- If a_m ≤ A, then min (a m) A = a m
          rw [min_eq_left (show a m ≤ A by linarith)]
          nlinarith [mul_nonneg (show 0 ≤ a n by linarith) (show 0 ≤ a m by linarith),
            mul_nonneg (show 0 ≤ (B : ℝ) by linarith) (show 0 ≤ (A : ℝ) by linarith)
            ]
        · -- If a_m > A, then min (a m) A = A
          rw [min_eq_right (show A ≤ a m by linarith)]
          nlinarith [mul_nonneg (show 0 ≤ a n by linarith) (show 0 ≤ a m by linarith),
            mul_nonneg (show 0 ≤ (B : ℝ) by linarith) (show 0 ≤ (A : ℝ) by linarith)
            ]
      · -- If a_n > A, then min (a n) A = A
        rw [min_eq_right (show A ≤ a n by linarith)]
        by_cases h8 : a m ≤ A
        · -- If a_m ≤ A, then min (a m) A = a m
          rw [min_eq_left (show a m ≤ A by linarith)]
          nlinarith [mul_nonneg (show 0 ≤ a n by linarith) (show 0 ≤ a m by linarith),
            mul_nonneg (show 0 ≤ (B : ℝ) by linarith) (show 0 ≤ (A : ℝ) by linarith),
            mul_pos (show 0 < (B : ℝ) by linarith) (show 0 < (A : ℝ) by linarith)
            ]
        · -- If a_m > A, then min (a m) A = A
          rw [min_eq_right (show A ≤ a m by linarith)]
          nlinarith [mul_nonneg (show 0 ≤ a n by linarith) (show 0 ≤ a m by linarith),
            mul_nonneg (show 0 ≤ (B : ℝ) by linarith) (show 0 ≤ (A : ℝ) by linarith),
            mul_pos (show 0 < (B : ℝ) by linarith) (show 0 < (A : ℝ) by linarith)
            ]
    have h6 : 0 < a n := by linarith
    have h7 : 0 < (min (a n) A : ℝ) := by
      have h8 : 1 ≤ a n := (ha n).1
      have h9 : 1 ≤ min (a n) A := by
        cases min_cases (a n) A with
        | inl h =>
          linarith
        | inr h =>
          nlinarith
      nlinarith
    have h8 : a m / a n ≤ B * (min (a m) A) / (min (a n) A) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    simpa using h8