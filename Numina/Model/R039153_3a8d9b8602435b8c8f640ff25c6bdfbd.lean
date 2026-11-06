import Mathlib

theorem algebra_125875 {f : ℝ → ℝ} (hf : ∀ x y, 0 < x → 0 < y → f x + f y = f (x * y))
    (hpos : ∀ x > 1, f x > 0) :
    (∀ x, 0 < x → f (1 / x) = -f x) ∧
    StrictMonoOn f (Set.Ioi 0) ∧
    (f 3 = 1 → ∀ a > 0, ∀ x, 0 < x → 2 * a - x > 0 → (f x - f (1 / (2 * a - x)) ≥ 2 ↔
      a ≥ 3 ∧ x ∈ Set.Icc (a - √(a^2 - 9)) (a + √(a^2 - 9)))) := by

  have h1 : ∀ x, 0 < x → f (1 / x) = -f x := by
    intro x hx
    have h2 : f x + f (1 / x) = f 1 := by
      specialize hf x (1 / x) hx (show 0 < 1 / x by positivity)
      have h3 : x * (1 / x) = 1 := by
        field_simp
      rw [h3] at hf
      linarith
    have h4 : f 1 = 0 := by
      have h5 : f 1 + f 1 = f 1 := by
        specialize hf 1 1 (by norm_num) (by norm_num)
        norm_num at hf ⊢
        linarith
      linarith
    linarith

  have h2 : StrictMonoOn f (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hx1 : 0 < x := by
      simpa using hx
    have hy1 : 0 < y := by
      simpa using hy
    have h3 : x < y := by
      simpa using hxy
    have h4 : y / x > 1 := by
      have h5 : 0 < x := hx1
      have h6 : x < y := h3
      have h7 : y / x > 1 := by
        apply (lt_div_iff₀ (by linarith)).mpr
        nlinarith
      linarith
    have h5 : f x + f (y / x) = f y := by
      have h6 : f x + f (y / x) = f (x * (y / x)) := by
        apply hf x (y / x) (by linarith) (by
          have : y / x > 0 := by
            apply div_pos
            all_goals linarith
          positivity
        )
      have h8 : x * (y / x) = y := by
        field_simp
      rw [h8] at h6
      linarith
    have h6 : f (y / x) > 0 := by
      apply hpos
      have : y / x > 1 := by
        have hx1 : 0 < x := by linarith
        have h3 : x < y := h3
        apply (lt_div_iff₀ (by linarith)).mpr
        nlinarith
      linarith
    have h7 : f y > f x := by
      nlinarith
    exact h7

  constructor
  · exact h1
  constructor
  · exact h2
  · intro h3
    intro a ha x hx1 hx2
    have hx3 : 0 < 2 * a - x := by linarith
    constructor
    · -- Assume $f(x) - f(1/(2a-x)) \geq 2$, prove $a \geq 3 \wedge x \in \text{Icc}(a - \sqrt(a^2 - 9))(a + \sqrt(a^2 - 9)))$
      intro h
      have h4 : f (2 * a - x) = -f (1 / (2 * a - x)) := by
        have h5 : f (1 / (2 * a - x)) = -f (2 * a - x) := by
          have h7 : 0 < 2 * a - x := by linarith
          have h8 : f (1 / (2 * a - x)) = -f (2 * a - x) := by
            specialize h1 (2 * a - x) (by linarith)
            linarith
          linarith
        linarith
      have h7 : f x + f (2 * a - x) ≥ 2 := by
        linarith [h4, h]
      have h8 : f (x * (2 * a - x)) ≥ 2 := by
        have h9 : f x + f (2 * a - x) = f (x * (2 * a - x)) := by
          have hx4 : 0 < x := by linarith
          have hy4 : 0 < 2 * a - x := by linarith
          specialize hf x (2 * a - x) (by linarith) (by linarith)
          linarith
        nlinarith
      have h9 : f 9 = 2 := by
        have h10 : f 3 + f 3 = f 9 := by
          specialize hf 3 3 (by norm_num) (by norm_num)
          norm_num at hf ⊢
          linarith
        rw [show f 3 = 1 by linarith [h3]] at h10
        linarith
      have ha1 : a ≥ 3 := by
        by_contra h
        push_neg at h
        have ha2 : x * (2 * a - x) < 9 := by
          nlinarith [sq_nonneg (x - a), sq_nonneg (a - 3), sq_nonneg (x - a), sq_nonneg (x - 3), sq_nonneg (x - (2 * a - x))]
        have ha3 : f (x * (2 * a - x)) < f 9 := by
          have h13 : x * (2 * a - x) > 0 := by
            nlinarith [mul_pos (show 0 < x by linarith) (show 0 < 2 * a - x by linarith)]
          have h14 : (9 : ℝ) > 0 := by norm_num
          have h15 : x * (2 * a - x) < (9 : ℝ) := by
            linarith
          apply h2 (show x * (2 * a - x) ∈ Set.Ioi (0 : ℝ) by
            simp
            all_goals nlinarith
          ) (show (9 : ℝ) ∈ Set.Ioi (0 : ℝ) by
            simp
          ) (by
            nlinarith
          )
        nlinarith [h9, ha3, h8]
      have hx4 : x * (2 * a - x) ≥ 9 := by
        by_contra h
        push_neg at h
        have h10 : f (x * (2 * a - x)) < 2 := by
          have h11 : x * (2 * a - x) < (9 : ℝ) := by
            linarith
          have h12 : f (x * (2 * a - x)) < f 9 := by
            have h13 : x * (2 * a - x) > 0 := by
              nlinarith [mul_pos (show 0 < x by linarith) (show 0 < 2 * a - x by linarith)]
            have h14 : (9 : ℝ) > 0 := by norm_num
            have h15 : x * (2 * a - x) < (9 : ℝ) := by
              linarith
            apply h2 (show x * (2 * a - x) ∈ Set.Ioi (0 : ℝ) by
              simp
              all_goals nlinarith
            ) (show (9 : ℝ) ∈ Set.Ioi (0 : ℝ) by
              simp
            ) (by
              nlinarith
            )
          have h13 : f 9 = 2 := h9
          linarith
        nlinarith
      have h12 : x ^ 2 - 2 * a * x + 9 ≤ 0 := by nlinarith [hx4]
      have h11 : x ≥ a - Real.sqrt (a ^ 2 - 9) := by
        nlinarith [Real.sqrt_nonneg (a ^ 2 - 9), Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 - 9 by nlinarith)]
      have h10 : x ≤ a + Real.sqrt (a ^ 2 - 9) := by
        nlinarith [Real.sqrt_nonneg (a ^ 2 - 9), Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 - 9 by nlinarith)]
      constructor
      · exact ha1
      · exact ⟨h11, h10⟩
    · -- Assume $a \geq 3 \wedge x \in \text{Icc}(a - \sqrt(a^2 - 9))(a + \sqrt(a^2 - 9)))$, prove $f(x) - f(1/(2a-x)) \geq 2$.
      rintro ⟨ha1, ⟨hx11, hx12⟩⟩
      have h9 : f 9 = 2 := by
        have h10 : f 3 + f 3 = f 9 := by
          specialize hf 3 3 (by norm_num) (by norm_num)
          norm_num at hf ⊢
          linarith
        rw [show f 3 = 1 by linarith [h3]] at h10
        linarith
      have hx4 : x ≥ a - Real.sqrt (a ^ 2 - 9) := by linarith
      have hx5 : x ≤ a + Real.sqrt (a ^ 2 - 9) := by linarith
      have h12 : x ^ 2 - 2 * a * x + 9 ≤ 0 := by
        nlinarith [Real.sqrt_nonneg (a ^ 2 - 9), Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 - 9 by nlinarith)]
      have hx4 : x * (2 * a - x) ≥ 9 := by
        nlinarith
      have h8 : f (x * (2 * a - x)) ≥ 2 := by
        have h9 : f 9 = 2 := h9
        have h10 : x * (2 * a - x) ≥ 9 := hx4
        have h11 : f (x * (2 * a - x)) ≥ f 9 := by
          have h12 : 9 > 0 := by nlinarith
          have h13 : x * (2 * a - x) > 0 := by
            nlinarith [mul_pos (show 0 < x by linarith) (show 0 < 2 * a - x by linarith)]
          have h14 : 9 > 0 := by norm_num
          have h15 : x * (2 * a - x) ≥ (9 : ℝ) := by linarith
          have h100 : f (x * (2 * a - x)) ≥ f 9 := by
            by_cases h99 : x * (2 * a - x) > (9 : ℝ)
            · have h100 : f (x * (2 * a - x)) > f 9 := by
                apply h2 (show 9 ∈ Set.Ioi (0 : ℝ) by
                  simp
                ) (show x * (2 * a - x) ∈ Set.Ioi (0 : ℝ) by
                  simp
                  all_goals nlinarith
                ) (by
                  nlinarith
                )
              nlinarith
            · -- $x * (2a - x) = 9$.
              have h101 : x * (2 * a - x) = (9 : ℝ) := by linarith
              rw [h101]
          exact h100
        nlinarith [h9]
      have h7 : f x + f (2 * a - x) ≥ 2 := by
        have h9 : f x + f (2 * a - x) = f (x * (2 * a - x)) := by
          have hx4 : 0 < x := by linarith
          have hy4 : 0 < 2 * a - x := by linarith
          specialize hf x (2 * a - x) (by linarith) (by linarith)
          linarith
        nlinarith
      have h4 : f (2 * a - x) = -f (1 / (2 * a - x)) := by
        have h5 : f (1 / (2 * a - x)) = -f (2 * a - x) := by
          have h7 : 0 < 2 * a - x := by linarith
          have h8 : f (1 / (2 * a - x)) = -f (2 * a - x) := by
            specialize h1 (2 * a - x) (by linarith)
            linarith
          linarith
        linarith
      nlinarith