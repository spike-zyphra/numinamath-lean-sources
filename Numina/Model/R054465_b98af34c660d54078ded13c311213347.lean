import Mathlib

theorem algebra_220966 {f : ℝ → ℝ} (hf : ∃ a b, f = fun x => a * x + b)
    (h : ∀ x, f (f x) = 4 * x + 1) :
    f = (fun x => 2 * x + 1 / 3) ∨ f = (fun x => -2 * x - 1) := by

  rcases hf with ⟨a, b, hfab⟩
  have eq1 := h 0
  simp [hfab] at eq1
  have eq2 := h 1
  simp [hfab] at eq2
  have hsq : a^2 = 4 := by
    nlinarith
  
  have ha : a = 2 ∨ a = -2 := by
    have h1 : a^2 - 4 = 0 := by linarith
    have h2 : (a - 2) * (a + 2) = 0 := by 
      linarith [h1]
    cases' (mul_eq_zero.1 h2) with h3 h4
    · left
      linarith
    · right
      linarith

  cases' ha with h1 h1

  · -- a = 2
    have b_val : b = 1/3 := by
      rw [h1] at eq1
      linarith
    left
    funext x
    simp [hfab, b_val, h1]
    <;> ring_nf <;> linarith

  · -- a = -2
    have b_val : b = -1 := by
      rw [h1] at eq1
      linarith
    right
    funext x
    simp [hfab, b_val, h1]
    <;> ring_nf <;> linarith