import Mathlib

theorem algebra_12265 {a : ℕ → ℝ} (ha : a 0 = 3 / 4) (ha1 : a 1 = 15)
    (hge : ∃ r, ∀ n, a n = a 0 * r ^ n) :
    IsLeast {n | 1 ≤ n ∧ ∃ (k : ℤ), 1000000 * k = a n } 6 := by
  rcases hge with ⟨r, hr⟩
  have h1 : a 1 = a 0 * r ^ 1 := hr 1
  rw [ha, ha1] at h1
  have hr20 : r = 20 := by
    norm_num at h1
    linarith
  have h2 : ∀ n, a n = (3 / 4 : ℝ) * (20 : ℝ) ^ n := by
    intro n
    specialize hr n
    rw [hr]
    rw [ha, hr20]
  constructor
  · -- Show 6 is in the set.
    constructor
    · norm_num
    · use 48
      have eq1 : a 6 = (48000000 : ℝ) := by
        rw [h2 6]
        norm_num
      have eq2 : (1000000 : ℝ) * (48 : ℤ) = (48000000 : ℝ) := by
        norm_num
      rw [eq1]
      exact_mod_cast eq2
  · -- Show there is no smaller n in the set.
    intro n hn
    rcases hn with ⟨hn1, ⟨k, hk⟩⟩
    by_contra h
    push_neg at h
    have hk_eq : (1000000 : ℝ) * (k : ℝ) = a n := by 
      exact_mod_cast hk
    have h400 : (4000000 : ℝ) * (k : ℝ) = 3 * (20 : ℝ) ^ n := by 
      have eq1 : (1000000 : ℝ) * (k : ℝ) = (3 / 4 : ℝ) * (20 : ℝ) ^ n := by
        rw [h2 n] at hk_eq
        linarith
      linarith
    have h500 : (4000000 : ℤ) * k = 3 * (20 : ℤ) ^ n := by 
      exact_mod_cast h400
    have h6 : n < 6 := by linarith
    interval_cases n <;> omega