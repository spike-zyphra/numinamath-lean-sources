import Mathlib

theorem algebra_311394 {x y : ℝ} (h : x + y = 1) :
    x ^ 100 / (x ^ 2 + y) + y ^ 2 / (x + y ^ 2) =
    x ^ 100 / (x + y ^ 2) + y ^ 2 / (x ^ 2 + y) := by 
  have h1 : y = 1 - x := by linarith
  have h2 : x ^ 2 + y = x + y ^ 2 := by 
    rw [show y = 1 - x by linarith [h1]]
    ring_nf
  -- Now that denominators are equal, we can show the expressions are equal
  have h3 : x ^ 100 / (x ^ 2 + y) + y ^ 2 / (x + y ^ 2) =
    x ^ 100 / (x + y ^ 2) + y ^ 2 / (x ^ 2 + y) := by
    have h4 : x ^ 2 + y = x + y ^ 2 := h2
    have h5 : x + y ^ 2 = x ^ 2 + y := by linarith [h4]
    rw [show x + y ^ 2 = x ^ 2 + y by linarith [h4]]
    all_goals ring_nf <;> norm_num 
  exact h3