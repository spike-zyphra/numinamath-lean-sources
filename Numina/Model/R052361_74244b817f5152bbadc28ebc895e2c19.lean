import Mathlib

theorem algebra_240571 (m z d : ℕ) (h : m + z + d = 1650)
    (h1 : z = (2 / 3 : ℚ) * m) (h2 : d = (3 / 8 : ℚ) * (m + z)) :
    m = 720 ∧ z = 480 ∧ d = 450 := by
  have eq1 : (m : ℚ) + (z : ℚ) + (d : ℚ) = (1650 : ℚ) := by
    exact_mod_cast h
  have h3 : 3 * (z : ℚ) = 2 * (m : ℚ) := by
    linarith [h1]
  have h4 : 3 * z = 2 * m := by
    exact_mod_cast h3
  have h5 : 8 * (d : ℚ) = 3 * ((m : ℚ) + (z : ℚ)) := by
    linarith [h2]
  have h6 : 8 * d = 3 * (m + z) := by
    exact_mod_cast h5
  have hm : m = 720 := by
    omega
  have hz : z = 480 := by
    omega
  have hd : d = 450 := by
    omega
  exact ⟨hm, hz, hd⟩