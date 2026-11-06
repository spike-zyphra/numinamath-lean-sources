import Mathlib

open Real

theorem inequalities_6522 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a + abs (a - b - c) ≥ abs (a - b) + abs (a - c) := by
  by_cases h : a - b - c ≥ 0
  · -- Case where $a - b - c \geq 0$, so $|a - b - c| = a - b - c$
    rw [abs_of_nonneg h]
    by_cases h1 : a - b ≥ 0
    · -- Subcase where $a - b \geq 0$, so $|a - b| = a - b$
      rw [abs_of_nonneg h1]
      by_cases h2 : a - c ≥ 0
      · -- Subcase where $a - c \geq 0$, so $|a - c| = a - c$
        rw [abs_of_nonneg h2]
        linarith
      · -- Subcase where $a - c < 0$, so $|a - c| = c - a$
        rw [abs_of_neg (lt_of_not_ge h2)]
        linarith
    · -- Subcase where $a - b < 0$, so $|a - b| = b - a$
      rw [abs_of_neg (lt_of_not_ge h1)]
      by_cases h2 : a - c ≥ 0
      · -- Subcase where $a - c \geq 0$, so $|a - c| = a - c$
        rw [abs_of_nonneg h2]
        linarith
      · -- Subcase where $a - c < 0$, so $|a - c| = c - a$
        rw [abs_of_neg (lt_of_not_ge h2)]
        linarith
  · -- Case where $a - b - c < 0$, so $|a - b - c| = b + c - a$
    rw [abs_of_neg (lt_of_not_ge h)]
    by_cases h1 : a - b ≥ 0
    · -- Subcase where $a - b \geq 0$, so $|a - b| = a - b$
      rw [abs_of_nonneg h1]
      by_cases h2 : a - c ≥ 0
      · -- Subcase where $a - c \geq 0$, so $|a - c| = a - c$
        rw [abs_of_nonneg h2]
        linarith
      · -- Subcase where $a - c < 0$, so $|a - c| = c - a$
        rw [abs_of_neg (lt_of_not_ge h2)]
        linarith
    · -- Subcase where $a - b < 0$, so $|a - b| = b - a$
      rw [abs_of_neg (lt_of_not_ge h1)]
      by_cases h2 : a - c ≥ 0
      · -- Subcase where $a - c \geq 0$, so $|a - c| = a - c$
        rw [abs_of_nonneg h2]
        linarith
      · -- Subcase where $a - c < 0$, so $|a - c| = c - a$
        rw [abs_of_neg (lt_of_not_ge h2)]
        linarith