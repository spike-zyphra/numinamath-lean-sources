import Mathlib

theorem algebra_111098 {f : ℝ → ℝ} (hf : ∃ a b, f = fun x => a * x + b)
    (hinc : ∀ x y, x < y → f x < f y) :
    ∃ g : ℝ → ℝ, (∃ c d, g = fun x => c * x + d) ∧
      (∀ x, f x = g (g x)) ∧ (∀ x y, x < y → g x < g y) := by

  rcases hf with ⟨a, b, hf_eq⟩
  have ha1 : a > 0 := by
    have h1 := hinc 0 1 (by norm_num)
    simp [hf_eq] at h1
    linarith

  use fun x => Real.sqrt a * x + b / (Real.sqrt a + 1)
  constructor
  · -- Show that g is a linear function
    use Real.sqrt a, b / (Real.sqrt a + 1)
    all_goals
      funext x
      simp
  constructor
  · -- Show that f x = g (g x) for all x
    intro x
    have h10 : Real.sqrt a ^ 2 = a := Real.sq_sqrt (show 0 ≤ a by linarith)
    have h11 : Real.sqrt a ≥ 0 := Real.sqrt_nonneg a
    have h12 : Real.sqrt a + 1 > 0 := by
      have h9 : Real.sqrt a ≥ 0 := Real.sqrt_nonneg a
      linarith
    have h13 : Real.sqrt a + 1 ≠ 0 := by linarith
    simp [hf_eq]
    have eq2 : Real.sqrt a * (Real.sqrt a * x + b / (Real.sqrt a + 1)) + b / (Real.sqrt a + 1) = a * x + b := by
      have eq3 : Real.sqrt a * (Real.sqrt a * x + b / (Real.sqrt a + 1)) + b / (Real.sqrt a + 1) =
        Real.sqrt a ^ 2 * x + Real.sqrt a * (b / (Real.sqrt a + 1)) + b / (Real.sqrt a + 1) := by
        ring
      rw [eq3]
      have eq4 : Real.sqrt a ^ 2 = a := Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith)
      rw [eq4]
      have eq5 : Real.sqrt a * (b / (Real.sqrt a + 1)) + b / (Real.sqrt a + 1) = b := by 
        have h14 : Real.sqrt a + 1 ≠ 0 := by
          have h14 : Real.sqrt a ≥ 0 := Real.sqrt_nonneg a
          linarith
        field_simp [(show Real.sqrt a + 1 ≠ 0 by exact h14)]
        <;> 
        nlinarith [Real.sqrt_nonneg a, Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith)]
      have eq6 : a * x + (Real.sqrt a * (b / (Real.sqrt a + 1)) + b / (Real.sqrt a + 1)) = a * x + b := by 
        linarith [eq5]
      linarith [eq6]
    linarith [eq2]
  · -- Show that g is strictly increasing
    intro x y hxy
    have hc : Real.sqrt a > 0 := by
      have ha3 : a > 0 := ha1
      have hc1 : Real.sqrt a > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      linarith
    have h2 : Real.sqrt a * x + b / (Real.sqrt a + 1) < Real.sqrt a * y + b / (Real.sqrt a + 1) := by
      have h3 : Real.sqrt a * x < Real.sqrt a * y := by
        apply mul_lt_mul_of_pos_left
        linarith
        all_goals
          have hc3 : Real.sqrt a > 0 := hc
          linarith [hc3]
      have h4 : b / (Real.sqrt a + 1) = b / (Real.sqrt a + 1) := by rfl
      linarith
    simpa using h2