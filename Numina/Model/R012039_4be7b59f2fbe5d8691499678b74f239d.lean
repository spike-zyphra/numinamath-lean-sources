import Mathlib

lemma lemma_1 {f : ℝ → ℝ} (hf : ∀ x y : ℝ, f (x + y) = f x * f y) (x : ℝ) : 0 ≤ f x := by
  
  specialize hf (x / 2) (x / 2)
  simp only [add_halves] at hf
  exact hf ▸ mul_self_nonneg (f (x / 2))

lemma lemma_2 {f : ℝ → ℝ} (hf : ∀ x y : ℝ, f (x + y) = f x * f y) (x : ℝ) (n : ℕ) (hn : 1 ≤ n) : f (n * x) = f x ^ n := by
  
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih => simp [add_one_mul, hf, ih, pow_succ] 

theorem algebra_170356 (f : ℝ → ℝ) (hfcont : Continuous f) (hf : ∀ x y : ℝ, f (x + y) = f x * f y) (h : f 2 = 5) :
    f 5 = 25 * √5 := by

  have f_nonneg : ∀ x : ℝ, 0 ≤ f x := by
    intro x
    apply lemma_1 hf x
  
  have f_zero : f 0 = 1 := by
    have h1 : f 0 = 1 := by
      have eq1 := hf 0 0
      have eq2 : f 0 = f 0 * f 0 := by
        norm_num at eq1 ⊢
        all_goals linarith
      by_cases h' : f 0 > 0
      · -- Assume f 0 > 0
        have eq3 : f 0 = 1 := by
          have eq4 : f 0 * (f 0 - 1) = 0 := by
            nlinarith
          cases (mul_eq_zero.1 eq4) with
          | inl h0 =>
            nlinarith
          | inr h1 =>
            linarith
        exact eq3
      · -- Assume not f 0 > 0
        have h_eq0 : f 0 = 0 := by
          nlinarith [f_nonneg 0]
        have h_eq1 : f 2 = f 2 * f 0 := by
          specialize hf 2 0
          simp [h_eq0] at hf ⊢
          linarith
        rw [h_eq0] at h_eq1 
        nlinarith [h, h_eq1]
    exact h1

  have f4 : f 4 = 25 := by
    specialize hf 2 2
    rw [show (2 : ℝ) + 2 = (4 : ℝ) by ring] at hf
    rw [h] at hf
    nlinarith [f_nonneg 2, f_nonneg 4, sq_nonneg (f 2 - 5), sq_nonneg (f 4 - 25)]

  have f1 : f 1 = Real.sqrt 5 := by
    have h1 := hf 1 1
    have h2 : f (1 + 1 : ℝ) = f 1 * f 1 := h1
    have h3 : f (1 + 1 : ℝ) = f (2 : ℝ) := by
      norm_num
    rw [h3] at h2
    rw [h] at h2
    have h4 : (f 1) ^ 2 = (5 : ℝ) := by nlinarith
    have h5 : 0 ≤ f 1 := by apply f_nonneg
    have h9 : f 1 = Real.sqrt 5 := by
      have h5yay : f 1 ≥ 0 := h5
      have h8 : (f 1) ^ 2 = (5 : ℝ) := h4
      have h9 : (f 1) = (Real.sqrt (5 : ℝ)) := by
        have h10 : 0 ≤ f 1 := h5yay
        have h11 : (f 1) ^ 2 = (5 : ℝ) := h8
        have h12 : 0 ≤ (Real.sqrt (5 : ℝ) : ℝ) := Real.sqrt_nonneg (5 : ℝ)
        nlinarith [h11, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
      exact h9
    exact h9

  have f5 : f 5 = f 4 * f 1 := by
    specialize hf 4 1
    norm_num at hf ⊢
    rw [hf]

  rw [f5, f4, f1]
  all_goals nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]