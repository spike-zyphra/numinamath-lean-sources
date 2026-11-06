import Mathlib

theorem number_theory_150068 (a b : ℕ → ℕ)
    (ha : ∀ n, a n = 2 * n + 1) (hb : ∀ n, b n = 5050 - 5 * n) :
    IsLeast {x | ∃ m, x = max (a m) (b m) - min (a m) (b m)} 2 := by
  constructor
  · -- Show that 2 is achievable by finding such an m
    use 721
    norm_num [ha, hb]
  · -- Show that 2 is the smallest
    intro x hx
    rcases hx with ⟨m, hm⟩
    rw [hm]
    by_cases h : a m ≤ b m
    · -- Case where a m ≤ b m
      rw [max_eq_right h, min_eq_left h]
      have h1 : a m ≤ b m := h
      have h2 : a m = 2 * m + 1 := ha m
      have h3 : b m = 5050 - 5 * m := hb m
      rw [h2] at h1
      rw [h3] at h1
      omega
    · -- Case where a m > b m
      rw [max_eq_left (le_of_not_ge h), min_eq_right (le_of_not_ge h)]
      have h2 : a m > b m := by linarith
      have h3 : a m = 2 * m + 1 := ha m
      have h4 : b m = 5050 - 5 * m := hb m
      rw [h3] at h2
      rw [h4] at h2
      omega