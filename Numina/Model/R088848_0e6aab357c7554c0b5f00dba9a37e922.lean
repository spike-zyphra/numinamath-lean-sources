import Mathlib

theorem algebra_285462 :
    ¬∃ a b c d : ℤ, (19^3 * a + 19^2 * b + 19 * c + d = 1) ∧ (62^3 * a + 62^2 * b + 62 * c + d = 2) := by 
  intro h 
  rcases h with ⟨a, b, c, d, h1, h2⟩
  have h3 : (62^3 * a + 62^2 * b + 62 * c + d) - (19^3 * a + 19^2 * b + 19 * c + d) = 2 - 1 := by 
    linarith 
  have h4 : (62^3 * a + 62^2 * b + 62 * c + d) - (19^3 * a + 19^2 * b + 19 * c + d) = 
          (62^3 - 19^3) * a + (62^2 - 19^2) * b + (62 - 19) * c := by 
    ring 
  rw [h4] at h3
  have h5 : (62^3 - 19^3) * a + (62^2 - 19^2) * b + (62 - 19) * c = 1 := by 
    linarith 
  have h6 : 43 * (5383 * a + 81 * b + c) = 1 := by 
    norm_num at h5 
    linarith 
  omega