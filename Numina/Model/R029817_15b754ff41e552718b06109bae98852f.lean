import Mathlib

theorem number_theory_7874 (a b c d : ℤ) (h₀ : a ≠ c) (h₁ : (a - c) ∣ a * b + c * d) :
    (a - c) ∣ a * d + b * c := by 
  have h2 : (a - c) ∣ (a * b + c * d) := h₁
  have h3 : (a - c) ∣ (a * d + b * c) := by
    have h4 : (a * d + b * c) = (a * b + c * d) + (a - c) * (d - b) := by
      ring
    rw [h4]
    apply dvd_add 
    · exact h₁
    · -- Show that $a - c$ divides $(a - c) * (d - b)$
      apply dvd_mul_right
  exact h3