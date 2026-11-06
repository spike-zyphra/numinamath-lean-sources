import Mathlib

theorem algebra_312797 {f : ℝ → ℝ} (hf : ∃ a b c, f = fun x => a * x ^ 2 + b * x + c)
    (h : ∀ x, f (x + 2) = f (-x + 2)) (h0 : f 0 = 1) (h1 : ∃ x1 x2, x1 ≠ x2 ∧ f x1 = 0 ∧ f x2 = 0 ∧ |x1 - x2| = 2 * Real.sqrt 2) :
    f = fun x => (1 / 2) * x ^ 2 - 2 * x + 1 := by
  rcases hf with ⟨a, b, c, hf_eq⟩
  have h2 : ∀ x : ℝ, a * (x + 2) ^ 2 + b * (x + 2) + c = a * (-x + 2) ^ 2 + b * (-x + 2) + c := by
    intro x
    have h3 : f (x + 2) = f (-x + 2) := h x
    simp [hf_eq] at h3 ⊢
    linarith

  have eq4 : b = -4 * a := by
    have eq1 := h2 0
    have eq2 := h2 1
    nlinarith

  have eq5 : c = 1 := by
    have h4 : f 0 = 1 := h0
    simp [hf_eq] at h4
    linarith

  rcases h1 with ⟨x1, x2, hx12, hx1, hx2, h3⟩

  have h_eq1 : a * x1 ^ 2 + b * x1 + c = 0 := by 
    have h4 : f x1 = 0 := hx1
    simp [hf_eq] at h4
    linarith

  have h_eq2 : a * x2 ^ 2 + b * x2 + c = 0 := by 
    have h4 : f x2 = 0 := hx2
    simp [hf_eq] at h4
    linarith

  have eq7 : a * (x1 ^ 2 - x2 ^ 2) + b * (x1 - x2) = 0 := by
    nlinarith

  have hx12' : x1 - x2 ≠ 0 := by
    intro h_eq
    apply hx12
    linarith

  have eq8 : a * (x1 + x2) + b = 0 := by 
    apply (mul_left_inj' hx12').mp 
    linarith

  have eq9 : a * (x1 + x2 - 4) = 0 := by
    nlinarith [eq4]

  cases (mul_eq_zero.mp eq9) with
  | inl ha0 =>
    -- Case 1: If $a = 0$, 
    have hb0 : b = 0 := by
      rw [ha0] at eq4 
      linarith 
    rw [ha0, hb0, eq5] at h_eq1 
    nlinarith
  | inr hx4 =>
    -- Case 2: If $x1 + x2 = 4$, 
    have h5 : (x1 - x2) ^ 2 = 8 := by
      have h6 : |x1 - x2| = 2 * Real.sqrt 2 := h3
      calc
        (x1 - x2) ^ 2 = ( |x1 - x2| )^2 := by rw [sq_abs]
        _ = (2 * Real.sqrt 2)^2 := by rw [h6] 
        _ = 4 * (Real.sqrt 2 ^ 2) := by ring 
        _ = 4 * (2) := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] 
        _ = 8 := by norm_num 
    have eq11 : x1 * x2 = 2 := by
      nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 + x2 - 4)]
    have eq12 : a * (x1 ^ 2 + x2 ^ 2) + b * (x1 + x2) + 2 * c = 0 := by
      nlinarith
    have eq13 : x1 ^ 2 + x2 ^ 2 = 12 := by
      nlinarith
    have ha2 : a = 1 / 2 := by 
      nlinarith [eq4, eq5]
    have hb2 : b = -2 := by
      rw [ha2] at eq4
      nlinarith
    funext x 
    simp [hf_eq, ha2, hb2, eq5]
    <;> ring