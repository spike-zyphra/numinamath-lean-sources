import Mathlib

theorem algebra_271058 {f : ℝ → ℝ} (hf : ∃ a b, f = fun x => a * x + b)
    (hfn : ∀ x, f^[10] x = 1024 * x + 1023) :
    f = (fun x => 2 * x + 1) ∨ f = (fun x => -2 * x - 3) := by
  rcases hf with ⟨a, b, hf⟩
  have eq1 := hfn 0
  simp [hf, Function.iterate_succ_apply'] at eq1 
  have eq2 := hfn 1
  simp [hf, Function.iterate_succ_apply'] at eq2 
  have h1 : a ^ 10 = 1024 := by
    nlinarith
  have h2 : a = 2 ∨ a = -2 := by 
    have h3 : a ^ 10 - 1024 = 0 := by
      nlinarith 
    have h4 : a ^ 10 - 1024 = (a ^ 2 - 4) * (a  ^ 8 + (4 : ℝ) * a ^ 6 + (16 : ℝ) * a ^ 4 + (64 : ℝ) * a ^ 2 + (256 : ℝ)) := by 
      ring
    rw [h4] at h3 
    cases (mul_eq_zero.1 h3) with 
    | inl h5 =>
      have h6 : a ^ 2 - 4 = 0 := h5
      have h7 : a ^ 2 = 4 := by linarith
      have : a = 2 ∨ a = -2 := by 
        have h : a ^ 2 = 4 := h7 
        have h8 : a = 2 ∨ a = -2 := by 
          apply eq_or_eq_neg_of_sq_eq_sq 
          norm_num 
          linarith 
        tauto 
      assumption 
    | inr h8 =>
      nlinarith [sq_nonneg (a ^ 4), sq_nonneg (a ^ 2 - 4), sq_nonneg (a ^ 2 + 4), sq_nonneg (a - 2), sq_nonneg (a + 2)]
  cases h2 with 
  | inl ha2 =>
    have h3 : b = 1 := by 
      rw [show a = 2 by linarith] at eq1 eq2
      nlinarith 
    left 
    funext x 
    simp [hf, ha2, h3]
  | inr ha2 =>
    have h3 : b = -3 := by 
      rw [show a = -2 by linarith] at eq1 eq2
      nlinarith 
    right 
    funext x 
    simp [hf, ha2, h3]
    all_goals ring