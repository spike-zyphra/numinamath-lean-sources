import Mathlib

theorem number_theory_6323
    (a b n : ℤ)
    (h₀ : a ∣ b * n)
    (h₁ : ∃ x y, a * x + b * y = 1) :
    a ∣ n := by 
  rcases h₁ with ⟨x, y, h₂⟩
  have eq1 : a * x + b * y = 1 := h₂
  have eq2 : n = n * (a * x + b * y) := by
    rw [eq1]
    all_goals ring
  have eq3 : n = n * (a * x) + n * (b * y) := by 
    linarith [eq2]
  have h4 : a ∣ n * (a * x) := by
    use n * x
    all_goals ring
  have h5 : a ∣ n * (b * y) := by
    have h0 : a ∣ b * n := h₀
    -- We need to show `a` divides `(b * (n * y))`
    have h7 : n * (b * y) = (b * n) * y := by 
      ring
    rw [h7] at *
    apply dvd_mul_of_dvd_left
    exact h0
  have h8 : a ∣ n * (a * x) + n * (b * y) := by
    apply dvd_add
    exact h4
    exact h5
  have h9 : n * (a * x) + n * (b * y) = n := by 
    linarith [eq3]
  rw [h9] at h8
  exact h8