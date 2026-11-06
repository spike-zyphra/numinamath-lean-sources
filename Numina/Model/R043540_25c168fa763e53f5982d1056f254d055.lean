import Mathlib

theorem algebra_115107 {a b : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + a * x + b)
    (A B : Set ℝ) (hA : A = {x | f x = x}) (hB : B = {x | f (f x) = x})
    (hA' : A = {-1, 3}) :
    B = {-1, Real.sqrt 3, -Real.sqrt 3, 3} := by
  have h1 : -1 ∈ A := by
    rw [hA']
    simp
  have h2 : (3 : ℝ) ∈ A := by
    rw [hA']
    simp
  have eq1 : f (-1) = -1 := by
    have h11 : -1 ∈ A := h1
    rw [hA] at h11
    simpa using h11
  have eq2 : f 3 = 3 := by
    have h22 : (3 : ℝ) ∈ A := h2
    rw [hA] at h22
    simpa using h22
  have eq3 : (-1 : ℝ) ^ 2 + a * (-1) + b = -1 := by
    rw [hf] at eq1
    linarith
  have eq4 : (3 : ℝ) ^ 2 + a * (3 : ℝ) + b = 3 := by
    rw [hf] at eq2
    linarith
  have ha : a = -1 := by
    nlinarith [eq3, eq4]
  have hb : b = -3 := by
    nlinarith [eq3, ha]
  ext x
  simp [hB]
  have eq5 : f x = x ^ 2 - x - 3 := by
    rw [hf]
    rw [ha, hb]
    all_goals ring
  have eq6 : f (f x) = (x ^ 2 - x - 3) ^ 2 - (x ^ 2 - x - 3) - 3 := by
    rw [eq5]
    rw [hf]
    all_goals rw [ha, hb]
    all_goals ring
  rw [eq6]
  constructor
  · -- Assume $f(f(x)) = x$, prove $x \in \{-1, \pm\sqrt{3},3\}$.
    intro h_eq
    have h_eq2 : (x + 1) * (x - 3) * (x ^ 2 - 3) = 0 := by
      nlinarith [sq_nonneg (x ^ 2 - x - 3), sq_nonneg (x ^ 2 - 3), sq_nonneg (x + 1), sq_nonneg (x - 3)]
    cases' (mul_eq_zero.mp h_eq2) with h1 h2
    cases' (mul_eq_zero.mp h1) with h3 h4
    · -- Case h3: x + 1 = 0
      have h7 : x = -1 := by linarith
      simp [h7]
    · -- Case h4: x - 3 = 0
      have h7 : x = 3 := by linarith
      simp [h7]
    · -- Case h2: x ^ 2 - 3 = 0
      have h5 : x ^ 2 - 3 = 0 := by
        linarith
      have h6 : x ^ 2 = 3 := by linarith
      have h7 : x = Real.sqrt 3 ∨ x = -Real.sqrt 3 := by
        apply eq_or_eq_neg_of_sq_eq_sq
        field_simp
        linarith
      cases h7 with
      | inl h8 =>
        simp [h8]
      | inr h8 =>
        simp [h8]
  · -- Assume $x \in \{-1, \pm\sqrt{3},3\}$, prove $f(f(x)) = x$.
    intro h
    rcases h with (rfl | rfl | rfl | rfl)
    · -- x = -1
      norm_num [eq5, ha, hb]
    · -- x = Real.sqrt 3
      have h8 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    · -- x = -Real.sqrt 3
      have h8 : (-Real.sqrt 3) ^ 2 = 3 := by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    · -- x = 3
      norm_num [eq5, ha, hb]