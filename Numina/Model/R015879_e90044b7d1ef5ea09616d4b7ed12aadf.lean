import Mathlib

theorem algebra_8820 {x : ℚ} (hx : x ≠ 0) (h : ∃ a : ℤ, x + 1/x = a) :
    ∃ b : ℤ, x^8 + 1/x^8 = b := by
  rcases h with ⟨a, ha⟩
  have h1 : x + 1 / x = (a : ℚ) := by exact_mod_cast ha
  have h2 : x^2 + 1 / x^2 = (a : ℚ)^2 - 2 := by 
    calc
      x^2 + 1 / x^2 = (x + 1 / x) ^ 2 - 2 := by 
        field_simp [hx]
        <;> ring
      _ = (a : ℚ)^2 - 2 := by 
        rw [h1]
  have h4 : x^4 + 1 / x^4 = ((a : ℚ)^2 - 2)^2 - 2 := by
    calc
      x^4 + 1 / x^4 = (x^2 + 1 / x^2) ^ 2 - 2 := by 
        field_simp [hx]
        <;> ring
      _ = ((a : ℚ)^2 - 2)^2 - 2 := by 
        rw [h2]
  have h8 : x^8 + 1 / x^8 = (((a : ℚ)^2 - 2)^2 - 2) ^ 2 - 2 := by
    calc
      x^8 + 1 / x^8 = (x^4 + 1 / x^4) ^ 2 - 2 := by 
        field_simp [hx]
        <;> ring
      _ = (((a : ℚ)^2 - 2)^2 - 2) ^ 2 - 2 := by 
        rw [h4]
  use ((a^2 - 2)^2 - 2)^2 - 2
  have h9 : x^8 + 1 / x^8 = ((a^2 - 2)^2 - 2)^2 - 2 := by 
    rw [h8]
    <;> ring_nf
  exact_mod_cast h9