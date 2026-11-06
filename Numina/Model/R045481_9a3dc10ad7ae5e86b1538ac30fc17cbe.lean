import Mathlib

theorem algebra_139321 {f g : ℝ → ℝ} (a : ℝ) (apos : 0 < a) (hf : ∃ k, k < 0 ∧ f = fun x => k * (x - a) ^ 2 + 5)
  (hg : ∃ k' b, 0 < k' ∧ g = fun x => k' * (x - b) ^ 2 - 2)
  (ga : g a = 25) (hfg : ∀ x, f x + g x = x ^ 2 + 16 * x + 13) :
  a = 1 ∧ g = fun x => 3 * x ^ 2 + 12 * x + 10 := by

  rcases hf with ⟨k, ⟨kneg, hf⟩⟩
  rcases hg with ⟨k', b, ⟨kp, hg⟩⟩
  have h1 := hfg a
  simp [hf, hg] at h1
  have h2 : g a = 25 := ga
  simp [hg] at h2
  -- From h2 and h1: k = 5 + g a = a^2 +16 * a +13
  -- Equation with a.
  have h1a : a^2 + 16 * a - 17 = 0 := by 
    nlinarith 
  -- Solve the quadratic for a >0
  have ha1 : a = 1 := by 
    have h3 : a^2 + 16 * a - 17 = 0 := h1a
    have : (a - 1) * (a + 17) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.1 this) with h4 h5
    · linarith 
    · linarith 
  -- Now to prove the second part of g
  have eq1 := hfg 0 
  simp [hf, hg] at eq1 
  rw [ha1] at eq1 
  -- Solving equations: k',b comes from. 
  have eq2 := hfg 1 
  simp [hf, hg] at eq2 
  rw [ha1] at eq2 
  have eq3 := hfg (-1) 
  simp [hf, hg] at eq3 
  rw [ha1] at eq3 
  -- Solving equations: k',b comes from.
  have h6 : k' * (1 - b) ^ 2 = 27 := by 
    nlinarith 
  -- Now solving method aligns.
  have h8 : k' = 3 := by 
    nlinarith [sq_nonneg (1 - b), sq_nonneg ((-1 - b) + b), sq_nonneg (b - 4), sq_nonneg (b + 2), sq_nonneg (b - 1), sq_nonneg (k), sq_pos_of_pos (kp)]
  have h9 : (1 - b) ^ 2 = 9 := by 
    nlinarith 
  have h10 : 1 - b = 3 ∨ 1 - b = -3 := by 
    have h8' : (1 - b) ^ 2 - 9 = 0 := by 
      nlinarith 
    have h11 : (1 - b - 3) * (1 - b + 3) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.1 h11) with h12 h13 
    · left 
      linarith 
    · right 
      linarith 
  cases' h10 with h11 h12 
  · -- Case 1 - b = 3, so b = -2 
    have hb1 : b = -2 := by 
      nlinarith 
    -- Checking consistency: k' = 3 and b = -2 from eq1
    -- k +3*(-2)^2 = 10 =k+12 =10 =>k=-2
    have h7 : k = -2 := by 
      rw [hb1] at eq1 
      nlinarith 
    -- We have k = -2. satisfies k <0
    have hk : k = -2 := h7 
    -- Final answer is a =1 and g(x) =3x^2 +12x +10
    constructor 
    · exact ha1 
    · funext x 
      simp [hg, hb1, h8] 
      <;> nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 1)]
  · -- Case 1 - b = -3, so b = 4 
    have hb1 : b = 4 := by 
      nlinarith 
    -- Checking consistency: k' = 3 and b = 4 from eq1
    -- k +3*(4)^2 =10 =>k +48 =10 =>k =-38
    have h7 : k = -38 := by 
      rw [hb1] at eq1 
      nlinarith 
    -- Now contradiction in eq3 :4*(-38) +3*(-1 -4)^2 =-152 +75=-77 \ne -5
    have h7' :4 * k + 3 * (-1 - b) ^ 2 = -5 := by 
      nlinarith 
    rw [hb1] at h7' 
    nlinarith