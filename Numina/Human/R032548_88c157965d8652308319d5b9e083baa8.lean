import Mathlib
import Aesop
open Set 
/-Given that 2 is an element of the set {0, a, a^2 - 3a + 2}, the value of the real number a is _______.-/
theorem algebra_9038 (a : ℝ) (h : 2 ∈ ({0, a, a^2 - 3 * a + 2}:Set ℝ))(h1: 0 ≠ a)(h2: a ≠ a^2 - 3 * a + 2)(h3: 0 ≠ a^2 - 3 * a + 2) : a = 3 := by
-- unfold condition h
simp at h
-- consider 3 cases 
rcases h with h1 | h2
-- for this case, a =2 have conflict
rw [← h1] at h3
norm_num at h3
-- solve equation
apply mul_left_cancel₀ (sub_ne_zero.mpr h1)
nlinarith
