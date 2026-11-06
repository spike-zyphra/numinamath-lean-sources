import Mathlib

/-The function $f(x)$ satisfies
\[f(x + y) = f(x) f(y)\]for all real numbers $x$ and $y.$  If $f(2) = 9,$ find $f(5).$-/
theorem algebra_18735 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x * f y) (h' : f 2 = 9) : f 5 = 243 := by
  -- Setting $x = 1$ and $y = 1,$ we get [f(2) = f(1) f(1),]so $f(1)^2 = 9.$ Then $f(1) = \pm 3.$
  have h1 : f 1 ^ 2 = 9 := by
    have h21 : f 2 = f 1 * f 1 := by 
      rw [←h 1 1]
      norm_num
    rw [h'] at h21
    nlinarith
  -- Setting $x = \frac{1}{2}$ and $y = \frac{1}{2},$ we get [f(1) = f \left( \frac{1}{2} \right) f \left( \frac{1}{2} \right) = f \left( \frac{1}{2} \right)^2 \ge 0,]
  have h1_pos : f 1 > 0 := by
    have h1_eq2 : f 1 = 3 ∨ f 1 = -3 := by
      have h : f 1 ^ 2 - 9 = 0 := by linarith
      have h_factor : (f 1 - 3) * (f 1 + 3) = 0 := by 
        linarith [h]
      cases (mul_eq_zero.mp h_factor) with
      | inl h3 => 
        left
        linarith 
      | inr h_neg3 => 
        right
        linarith
    cases h1_eq2 with
    | inl h3 => 
      nlinarith
    | inr h_neg3 => 
      have h1_nonpos : f 1 ≤ 0 := by linarith 
      have h_half : f (1 / 2 : ℝ) ^ 2 = -3 := by
        have h1_eq : f 1 = f (1 / 2 : ℝ) * f (1 / 2 : ℝ) := by 
          rw [←h (1 / 2 : ℝ) (1 / 2 : ℝ)]
          norm_num
        rw [h_neg3] at h1_eq
        nlinarith 
      have h_contra : f (1 / 2 : ℝ) ^ 2 ≥ 0 := by 
        apply sq_nonneg 
      nlinarith [h_half, h_contra]
  -- so $f(1) = 3.$
  have h1_eq : f 1 = 3 := by 
    have h : f 1 ^ 2 - 9 = 0 := by linarith
    have h_factor : (f 1 - 3) * (f 1 + 3) = 0 := by 
      linarith [h]
    cases (mul_eq_zero.mp h_factor) with
    | inl h3 => 
      linarith 
    | inr h_neg3 => 
      have h1_nonpos : f 1 ≤ 0 := by nlinarith 
      nlinarith [h1_pos, h_neg3]
  -- Setting $x = 1$ and $y = 2,$ we get [f(3) = f(1) f(2) = 27.
  have h3 : f 3 = 27 := by 
    have h3_eq : f 3 = f 2 * f 1 := by 
      rw [←h 2 1]
      norm_num
    rw [h'] at h3_eq
    rw [h1_eq] at h3_eq
    linarith
  -- Setting $x = 2$ and $y = 3,$ we get [f(5) = f(2) f(3) = \boxed{243}.
  have h4 : f 4 = 81 := by 
    have h4_eq : f 4 = f 3 * f 1 := by 
      rw [←h 3 1]
      norm_num
    rw [h3] at h4_eq
    rw [h1_eq] at h4_eq
    linarith
  have h5 : f 5 = 243 := by 
    have h5_eq : f 5 = f 4 * f 1 := by 
      rw [←h 4 1]
      norm_num
    rw [h4] at h5_eq
    rw [h1_eq] at h5_eq
    linarith
  exact h5