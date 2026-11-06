import Mathlib

theorem number_theory_295690 (n : ℤ) (hn : n ≥ 0) :
    (20 * n + 2) ∣ (2023 * n + 210) ↔ n = 0 := by
  constructor
  · -- Assume (20 * n + 2) divides (2023 * n + 210) then n = 0.
    intro h
    have h1 : (20 * n + 2) ∣ (2023 * n + 210) := h
    have h2 : (20 * n + 2) ∣ (154 : ℤ) := by
      have h3 : (20 * n + 2) ∣ (20 * (2023 * n + 210) - 2023 * (20 * n + 2)) := by
        apply Dvd.dvd.sub
        · -- Show that (20 * n + 2) divides 20 * (2023 * n + 210)
          apply Dvd.dvd.mul_left
          exact h1
        · -- Show that (20 * n + 2) divides 2023 * (20 * n + 2)
          apply Dvd.dvd.mul_left
          simp
      have h4 : 20 * (2023 * n + 210) - 2023 * (20 * n + 2) = (154 : ℤ) := by
        linarith
      rw [h4] at h3
      exact h3
    have h4 : (20 * n + 2) ≤ (154 : ℤ) := by
      apply Int.le_of_dvd (by norm_num) h2
    have h5 : n ≤ 7 := by
      omega
    interval_cases n <;> norm_num at h1 h2 h4 ⊢
    <;> omega
  · -- Assume n = 0, then (20 * n + 2) divides (2023 * n + 210).
    intro h_eq
    rw [h_eq]
    norm_num