import Mathlib

theorem algebra_196287 {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ x → 0 ≤ f x)
    (h : ∀ a b c, 0 ≤ a → 0 ≤ b → 0 ≤ c → f (a ^ 3) + f (b ^ 3) + f (c ^ 3) = 3 * f a * f b * f c)
    (h1 : f 1 ≠ 1) : f 2019 = 0 := by
  have h2 := h 1 1 1 (by norm_num) (by norm_num) (by norm_num)
  have h3 : f 1 = (f 1) ^ 3 := by
    ring_nf at h2 ⊢
    linarith 
  have h4 : f 1 = 0 := by
    have h5 : (f 1) ^ 3 - f 1 = 0 := by
      nlinarith 
    have h6 : f 1 * ((f 1) ^ 2 - 1) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Case f 1 = 0
      linarith 
    · -- Case (f 1) ^ 2 - 1 = 0
      have h8' : (f 1) ^ 2 = 1 := by linarith 
      have h9 : f 1 = 1 ∨ f 1 = -1 := by 
        rw [sq_eq_one_iff] at h8'
        exact h8'
      cases' h9 with h91 h91
      · -- Case f 1 = 1
        tauto 
      · -- Case f 1 = -1
        have h92 : 0 ≤ f 1 := hf 1 (by norm_num)
        linarith 
  -- First prove that f(b ^ 3) + f(c ^ 3) = 0 for all b, c ≥ 0.
  have eq1 : ∀ b c : ℝ, (0 ≤ b → 0 ≤ c → f (b ^ 3) + f (c ^ 3) = 0) := by 
    intro b c hb hc
    have eq2 := h 1 b c (by norm_num) hb hc 
    simp [h4] at eq2 ⊢
    linarith 
  -- From eq1, we can derive that f(x^3) = 0 for all x ≥ 0.
  have h6 : ∀ (x : ℝ), 0 ≤ x → f (x ^ 3) = 0 := by
    intro x hx
    have eq3 := eq1 x (0 : ℝ) hx (by norm_num)
    -- Show $f(0^3) = 0$ by setting b = c = 0 in eq1
    have eq5 : f ((0 : ℝ) ^ 3) = 0 := by
      have eq6 := eq1 (0 : ℝ) (0 : ℝ) (by norm_num) (by norm_num)
      norm_num at eq6 ⊢
      all_goals linarith 
    have hx3 : f (x ^ 3) = 0 := by
      rw [eq5] at eq3 
      linarith [show f (x ^ 3) ≥ 0 by apply hf (x ^ 3) (by positivity)]
    exact hx3 
  -- Final part : f(2019)  = 0
  have h8 : f (( (2019 : ℝ) ^ (1 / 3 : ℝ) ) ^ 3) = 0 := by 
    -- Show $f(x^3) = 0$ for the specific real number x = (2019)^(1/3).
    have hx0 : 0 ≤ (2019 : ℝ) ^ (1 / 3 : ℝ) := by 
      apply Real.rpow_nonneg 
      norm_num 
    apply h6 ((2019 : ℝ) ^ (1 / 3 : ℝ)) hx0 
  -- Simplify the base to 2019.
  have h9 : ( (2019 : ℝ) ^ (1 / 3 : ℝ) ) ^ 3 = (2019 : ℝ) := by 
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num 
    all_goals norm_num 
  rw [h9] at h8
  linarith