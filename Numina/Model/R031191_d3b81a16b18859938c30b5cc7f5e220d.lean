import Mathlib

theorem algebra_10764 (f : ℝ → ℝ) (hf : f = fun x => 8 * x ^ 2 - 38 * x + 35) :
    IsLeast {x | f x = 0} 1.25 := by
  have h1 : ∀ x, f x = 8 * x ^ 2 - 38 * x + 35 := by 
    intro x
    rw [hf]
  have h2 : f 1.25 = 0 := by
    rw [h1]
    norm_num
  have h3 : 1.25 ∈ {x | f x = 0} := by
    simpa using h2
  have h4 : ∀ x, f x = 0 → 1.25 ≤ x := by
    intro x hx
    have eq : f x = 8 * x ^ 2 - 38 * x + 35 := h1 x
    rw [eq] at hx
    have h5 : (x - 1.25) * (x - 3.5) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h5) with h6 h7
    · -- Case $x - 1.25 = 0$
      have hx1 : x = (1.25 : ℝ) := by
        linarith
      linarith
    · -- Case $x - 3.5 = 0$
      have hx2 : x = (3.5 : ℝ) := by
        linarith
      linarith
  constructor 
  · exact h3
  · intro x hx
    have hx1 : f x = 0 := by 
      simpa using hx
    have hx2 : 1.25 ≤ x := h4 x hx1
    linarith