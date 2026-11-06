import Mathlib

theorem algebra_321948 (f : ℝ → ℝ) (h₀ : ∀ x, f (f x - 3 ^ x) = 4)
    (h₁ : ∀ x y, x < y → f x < f y) : f 2 = 10 := by

  have h2 : ∀ x y, f x < f y → x < y := by
    intro x y h
    by_contra h3
    push_neg at h3
    have h4 : x ≥ y := by linarith
    by_cases h5 : x = y
    · 
      rw [h5] at h
      linarith
    · 
      have h6 : x > y := by
        by_contra h7
        push_neg at h7
        have h8 : x = y := by linarith
        contradiction
      have h7 : f x > f y := by
        apply h₁
        linarith
      linarith

  have h3 : ∀ x y : ℝ, f x - 3 ^ x = f y - 3 ^ y := by
    intro x y
    by_cases h4 : f x - 3 ^ x < f y - 3 ^ y
    · 
      have h5 : f (f x - 3 ^ x) < f (f y - 3 ^ y) := by 
        apply h₁
        linarith [h4]
      have h6 : f (f x - 3 ^ x) = 4 := h₀ x
      have h7 : f (f y - 3 ^ y) = 4 := h₀ y
      linarith [h5, h6, h7]
    · 
      by_cases h5 : f x - 3 ^ x > f y - 3 ^ y
      · 
        have h6 : f (f x - 3 ^ x) > f (f y - 3 ^ y) := by 
          apply h₁
          linarith [h5]
        have h7 : f (f x - 3 ^ x) = 4 := h₀ x
        have h8 : f (f y - 3 ^ y) = 4 := h₀ y
        linarith [h6, h7, h8]
      · 
        linarith

  have h4 : ∃ c : ℝ, ∀ x, f x = 3 ^ x + c := by
    use f 0 - 3 ^ (0 : ℝ)
    intro x
    have h5 : f x - 3 ^ x = f 0 - 3 ^ (0 : ℝ) := by
      specialize h3 x 0
      simpa using h3
    linarith

  rcases h4 with ⟨c, hc⟩
  have h5 : f 0 = 1 + c := by
    specialize hc 0
    norm_num at hc ⊢
    linarith

  have h6 : f c = 4 := by
    specialize h₀ 0
    rw [hc 0] at h₀
    norm_num at h₀ ⊢
    linarith

  have h7 : f c = 3 ^ c + c := by
    specialize hc c
    linarith

  have hc1 : c = 1 := by
    rw [h7] at h6
    by_cases h8 : c < 1
    · 
      have h81 : (3 : ℝ) ^ (c : ℝ) < (3 : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_lt_rpow_of_exponent_lt
        all_goals linarith
      have h82 : (3 : ℝ) ^ (c : ℝ) < (3 : ℝ) := by
        rw [show (3 : ℝ) ^ (1 : ℝ) = (3 : ℝ) by norm_num] at h81
        linarith
      have h83 : (3 : ℝ) ^ (c : ℝ) + (c : ℝ) < (4 : ℝ) := by
        linarith [h8, h82]
      linarith [h83, h6]
    · 
      by_cases h9 : c > 1
      · 
        have h91 : (3 : ℝ) ^ (c : ℝ) > (3 : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals linarith
        have h92 : (3 : ℝ) ^ (c : ℝ) > (3 : ℝ) := by
          rw [show (3 : ℝ) ^ (1 : ℝ) = (3 : ℝ) by norm_num] at h91
          linarith
        have h93 : (3 : ℝ) ^ (c : ℝ) + (c : ℝ) > (4 : ℝ) := by
          linarith [h9, h92]
        linarith [h93, h6]
      · 
        linarith

  have h8 : f 2 = 3 ^ (2 : ℝ) + (1 : ℝ) := by
    specialize hc 2
    rw [hc]
    rw [hc1]
    all_goals linarith
  have h9 : f 2 = 10 := by
    rw [h8]
    norm_num
  exact h9