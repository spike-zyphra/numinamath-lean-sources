import Mathlib

theorem number_theory_80527 {b c n : ℤ} (hn : n ≠ 0) (f : ℤ → ℤ) (hf : ∀ x, f x = x ^ 2 + b * x + c)
    (k1 k2 k3 : ℤ) (hdiv : n ∣ f k1 ∧ n ∣ f k2 ∧ n ∣ f k3) :
    n ∣ (k1 - k2) * (k2 - k3) * (k3 - k1) := by
  rcases hdiv with ⟨h1, h2, h3⟩
  have eq1 : f k1 = k1 ^ 2 + b * k1 + c := hf k1
  have eq2 : f k2 = k2 ^ 2 + b * k2 + c := hf k2
  have eq3 : f k3 = k3 ^ 2 + b * k3 + c := hf k3
  rw [eq1] at h1
  rw [eq2] at h2
  rw [eq3] at h3

  have h4 : n ∣ (k1 ^ 2 + b * k1 + c) - (k2 ^ 2 + b * k2 + c) := by
    exact Int.dvd_sub h1 h2
  have h6 : n ∣ (k3 ^ 2 + b * k3 + c) - (k1 ^ 2 + b * k1 + c) := by
    exact Int.dvd_sub h3 h1

  have eq10 : (k1 - k2) * (k2 - k3) * (k3 - k1) = 
    ((k1 ^ 2 + b * k1 + c) - (k2 ^ 2 + b * k2 + c)) * (k3 - k1) - 
    ((k3 ^ 2 + b * k3 + c) - (k1 ^ 2 + b * k1 + c)) * (k1 - k2) := by 
    ring_nf

  have h12 : n ∣ ((k1 ^ 2 + b * k1 + c) - (k2 ^ 2 + b * k2 + c)) * (k3 - k1) := by
    exact dvd_mul_of_dvd_left h4 (k3 - k1)
  have h13 : n ∣ ((k3 ^ 2 + b * k3 + c) - (k1 ^ 2 + b * k1 + c)) * (k1 - k2) := by
    exact dvd_mul_of_dvd_left h6 (k1 - k2)

  have h14 : n ∣ ((k1 ^ 2 + b * k1 + c) - (k2 ^ 2 + b * k2 + c)) * (k3 - k1) - 
    ((k3 ^ 2 + b * k3 + c) - (k1 ^ 2 + b * k1 + c)) * (k1 - k2) := by 
    exact Int.dvd_sub h12 h13

  rw [eq10] at *
  exact h14