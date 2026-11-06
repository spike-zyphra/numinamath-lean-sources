import Mathlib

theorem number_theory_38088 (f : ℤ → ℤ) (hf : ∀ n, f n = n ^ 5 - 5 * n ^ 3 + 4 * n) :
    IsGreatest {x | ∀ n, x ∣ f n} 120 := by
  constructor
  · -- Show that 120 is indeed in the set.
    show ∀ n, 120 ∣ f n
    intro n
    rw [hf]
    have h1 : n ^ 5 - 5 * n ^ 3 + 4 * n = n * (n - 1) * (n + 1) * (n - 2) * (n + 2) := by
      ring
    rw [h1]
    have h5 : 120 ∣ n * (n - 1) * (n + 1) * (n - 2) * (n + 2) := by
      -- Show that it divisible by 8, 3, and 5. 
      have h2 : (n * (n - 1) * (n + 1) * (n - 2) * (n + 2)) % 8 = 0 := by
        have h3 : n % 8 = 0 ∨ n % 8 = 1 ∨ n % 8 = 2 ∨ n % 8 = 3 ∨ n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7 := by
          omega
        rcases h3 with (h | h | h | h | h | h | h | h) <;> simp [h, Int.mul_emod, Int.add_emod, Int.sub_emod]
      have h3 : (n * (n - 1) * (n + 1) * (n - 2) * (n + 2)) % 3 = 0 := by
        have h4 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
          omega
        rcases h4 with (h | h | h) <;> simp [h, Int.mul_emod, Int.add_emod, Int.sub_emod]
      have h4 : (n * (n - 1) * (n + 1) * (n - 2) * (n + 2)) % 5 = 0 := by
        have h5 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
          omega
        rcases h5 with (h | h | h | h | h) <;> simp [h, Int.mul_emod, Int.add_emod, Int.sub_emod]
      omega
    exact h5
  · -- Show that 120 is greatest in the set.
    intro x hx
    have h1 : ∀ n, x ∣ f n := hx
    have h2 := h1 3
    have h3 : f 3 = 120 := by
      rw [hf]
      norm_num
    rw [h3] at h2
    have h4 : x ∣ 120 := h2
    have h5 : x ≤ 120 := by
      apply Int.le_of_dvd (by norm_num) h4
    linarith