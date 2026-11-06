import Mathlib

theorem algebra_9410 {a b : ℤ} {c d: ℚ} (ha : IsLeast {x : ℤ | x > 0 } a)
    (hb : IsGreatest {x : ℤ | x < 0 } b)
    (hc : IsLeast {x : ℚ | ∃ y : ℚ, x = abs y} c ) (hd : d ≠ 0 ∧ d = d⁻¹) :
    a^2 - b^2 + 2 * d - c = 2 ∨ a^2 - b^2 + 2 * d - c = -2 := by
  have ha1 : a = 1 := by
    have h1 : a > 0 := by 
      have h1 : a ∈ ({x : ℤ | x > 0 }) := by
        exact ha.1
      simpa using h1
    have h2 : ∀ x : ℤ, x ∈ ({x : ℤ | x > 0 }) → a ≤ x := by 
      apply ha.2
    have h3 := h2 1 (by norm_num)
    norm_num at h3
    linarith
  have hb1 : b = -1 := by
    have h1 : b < 0 := by 
      have h1 : b ∈ ({x : ℤ | x < 0 }) := by
        exact hb.1
      simpa using h1
    have h2 : ∀ x : ℤ, x ∈ ({x : ℤ | x < 0 }) → x ≤ b := by 
      apply hb.2
    have h3 := h2 (-1) (by norm_num)
    norm_num at h3
    linarith
  have hc1 : c = (0 : ℚ) := by 
    have h1 : ∃ y : ℚ, c = abs y := by
      simpa using hc.1
    rcases h1 with ⟨y, hy⟩
    have h2 : ∀ x : ℚ, (∃ y : ℚ, x = abs y) → c ≤ x := by 
      apply hc.2
    have h3 := h2 (0 : ℚ) ⟨0, by norm_num⟩
    have h4 : c ≤ (0 : ℚ) := by 
      simpa using h3
    have h5 : (0 : ℚ) ≤ c := by 
      have h5 : abs y ≥ 0 := by positivity
      linarith [show c = abs y by linarith [hy]]
    linarith [h4, h5]
  have hd1 : d = 1 ∨ d = -1 := by
    rcases hd with ⟨hne, heq⟩
    field_simp [hne] at heq ⊢
    have : d^2 - 1 = 0 := by linarith
    have : (d - 1) * (d + 1) = 0 := by linarith
    cases (mul_eq_zero.mp this) with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith
  have ha2 : (a : ℚ) = (1 : ℚ) := by exact_mod_cast ha1
  have hb2 : (b : ℚ) = (-1 : ℚ) := by exact_mod_cast hb1
  have hc2 : (c : ℚ) = (0 : ℚ) := by exact_mod_cast hc1
  rcases hd1 with (hd1 | hd1)
  · -- If d = 1, compute the expression
    have hd2 : d = (1 : ℚ) := hd1
    have h : (a : ℚ)^2 - (b : ℚ)^2 + 2 * d - c = 2 := by
      rw [ha2, hb2, hd2, hc2]
      norm_num
    left
    exact_mod_cast h
  · -- If d = -1, compute the expression
    have hd2 : d = (-1 : ℚ) := hd1
    have h : (a : ℚ)^2 - (b : ℚ)^2 + 2 * d - c = -2 := by
      rw [ha2, hb2, hd2, hc2]
      norm_num
    right
    exact_mod_cast h