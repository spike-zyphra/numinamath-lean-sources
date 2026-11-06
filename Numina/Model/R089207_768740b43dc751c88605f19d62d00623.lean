import Mathlib

theorem algebra_316482 (a : ℕ) (ha : a > 0) (h : ∃ x : ℕ, x > 0 ∧ (5/2 : ℝ)*x-a=(8/5 : ℝ)*x+142) :
    a ≥ 2 := by
  rcases h with ⟨x, hx_pos, heq⟩
  by_contra h'
  push_neg at h'
  -- However, since a > 0, this implies a = 1.
  have ha1 : a = 1 := by
    omega
  have h_eq : (a : ℝ) = (1 : ℝ) := by
    exact_mod_cast ha1
  rw [h_eq] at heq
  -- Let's compute x in this equation.
  -- h_eq now is 5/2*x - 1 = 8/5*x + 142
  -- Multiply both sides by 10 to clear fractions.
  -- 25x - 10 = 16x + 1420
  -- So 9x = 1430
  -- So x = 1430 / 9
  -- However 1430 divided by 9 isn't an integer.
  -- Therefore, we have a contradiction
  -- First, find x from the equation.
  have h_eq2 : (x : ℝ) = (1430 / 9 : ℝ) := by
    linarith

  have h_eq3 : 9 * (x : ℝ) = (1430 : ℝ) := by
    field_simp at h_eq2
    linarith
  
  have : 9 * x = 1430 := by
    norm_num at h_eq3 ⊢
    exact_mod_cast h_eq3
  
  omega