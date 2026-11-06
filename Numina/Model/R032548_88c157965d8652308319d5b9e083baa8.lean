import Mathlib
import Aesop
open Set 

theorem algebra_9038 (a : ℝ) (h : 2 ∈ ({0, a, a^2 - 3 * a + 2}:Set ℝ))(h1: 0 ≠ a)(h2: a ≠ a^2 - 3 * a + 2)(h3: 0 ≠ a^2 - 3 * a + 2) : a = 3 := by
  have h4 : 2 = (0 : ℝ) ∨ 2 = a ∨ 2 = a^2 - 3 * a + 2 := by
    simp [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    tauto
  rcases h4 with (h5 | h6 | h7)
  · -- Case 2 = 0 
    exfalso 
    linarith 
  · -- Case 2 = a 
    exfalso
    have ha : a = 2 := by linarith 
    have ha2 : a^2 - 3 * a + 2 = (0 : ℝ) := by 
      rw [ha]
      norm_num 
    rw [ha2] at h3 
    norm_num at h3 
  · -- Case 2 = a^2 - 3*a + 2 
    have eq1 : 2 = a^2 - 3 * a + 2 := by 
      simpa using h7 
    have eq2 : a^2 - 3 * a = 0 := by 
      linarith 
    have eq3 : a * (a - 3) = 0 := by 
      linarith 
    cases' (mul_eq_zero.mp eq3) with h8 h9 
    · -- Case h8 : a = 0 
      exfalso 
      apply h1 
      linarith 
    · -- Case h9 : a - 3 = 0 
      linarith