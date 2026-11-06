import Mathlib

/- Find, with proof, all functions $f: \mathbb{R} \backslash\{0\} \rightarrow \mathbb{R}$ such that

$$
f(x)^{2}-f(y) f(z)=x(x+y+z)(f(x)+f(y)+f(z))
$$

for all real $x, y, z$ such that $x y z=1$.-/
theorem algebra_610474 (f : ℝ → ℝ) :
    (∀ x y z, x * y * z = 1 → f x ^ 2 - f y * f z = x * (x + y + z) * (f x + f y + f z)) ↔ ((∀ x ≠ 0, f x = 0) ∨ (∀ x ≠ 0, f x = x ^ 2 - 1 / x)) := by
  -- Break the goal into two parts.
  apply Iff.intro
  . -- First show that the condition implies the two solutions.
    intro h₀
    -- Show that f(1) = 0.
    have h₁ : f 1 = 0 := by
      -- Substitute x = y = z = 1 into the functional equation.
      specialize h₀ 1 1 1 (by norm_num)
      norm_num [pow_two] at h₀
      linarith only [h₀]
    -- Show that f(x) = 0 or f(x) = x² - 1/x for each x ≠ 0.
    have h₂ (x : ℝ) : x ≠ 0 → (f x = 0 ∨ f x = x ^ 2 - 1 / x) := by
      intro hx
      by_cases hf : f x = 0
      . -- If f(x) = 0, it is directly the left case.
        tauto
      . -- Suppose f(x) ≠ 0.
        -- Substitute (x, y, z) = (x, 1, 1/x) into the functional equation.
        have h₃ := h₀ x 1 (1 / x) (by field_simp)
        -- Substitute (x, y, z) = (1, x, 1/x) into the functional equation.
        have h₄ := h₀ 1 x (1 / x) (by field_simp)
        simp [h₁, -one_div] at h₃ h₄
        -- Multiply both sides of h₄ by x.
        replace h₄ := congr_arg (x * ·) h₄
        simp only at h₄
        -- We have f(x) = 0 or f(1/x) = -f(x) / x, the former case is rejected.
        have h₅ : f x * (f x + x * f (1 / x)) = 0 := by
          field_simp at h₃ h₄
          linarith
        simp [hf, -one_div] at h₅
        -- Plug it into h₄ to get f(x) = x² - 1/x.
        replace h₅ : f (1 / x) = -f x / x := by
          field_simp
          linarith
        have h₆ : x * f x * (f x - (x ^ 2 - 1 / x)) = 0 := by
          rw [h₅] at h₄
          field_simp at h₄ ⊢
          linarith
        simp [hx, hf, -one_div] at h₆
        rw [sub_eq_zero] at h₆
        tauto
    -- Consider two cases: f(x) ≠ 0 ∀ x ∉ {0, 1}, and otherwise.
    by_cases h₃ : ∀ x, x ≠ 0 → x ≠ 1 → f x ≠ 0
    . -- If f(x) ≠ 0 for all x ≠ 0, 1, then f(x) = x² - 1/x.
      right
      intro x hx
      by_cases hx₁ : x = 1
      . -- If x = 1, f(1) = 0.
        norm_num [hx₁, h₁]
      . -- Otherwise, f(x) = x² - 1/x.
        specialize h₂ x hx
        simp [h₃ x hx hx₁, -one_div] at h₂
        exact h₂
    . left
      -- Assume not, then let t ≠ 1 such that f(t) = 0.
      simp at h₃
      obtain ⟨t, ht₀, ht₁, ht₂⟩ := h₃
      -- We shall show that f(x) = 0 ∀ x ≠ 0.
      have h₄ : ∀ x, x ≠ 0 → f x = 0 := by
        intro x hx
        -- Substitute (x, y, z) = (x, t, 1/tx) in the functional equation.
        have h₄ := h₀ x t (1 / (t * x)) (by field_simp; ac_rfl)
        -- Substitute (x, y, z) = (t, x, 1/tx) in the functional equation.
        have h₅ := h₀ t x (1 / (t * x)) (by field_simp)
        -- Multiply both sides of h₄ by t, both sides of h₅ by x.
        replace h₄ := congr_arg (t * ·) h₄
        -- Multiply both sides of h₅ by x and simplify the two equations using f(t) = 0.
        replace h₅ := congr_arg (x * ·) h₅
        simp only at h₄ h₅
        rw [ht₂] at h₄ h₅
        -- Now we get an equality tf(x)² = -xf(x)f(1/tx), or f(x) (tf(x) + xf(1/tx)) = 0.
        have h₆ : (f x) * (t * f x + x * f (1 / (t * x))) = 0 := by
          linarith
        -- If f(x) ≠ 0, then f(1/tx) = -(t/x)f(x).
        by_contra!
        have h₇ : f (1 / (t * x)) = -(t / x) * f x := by
          simp [this, -one_div] at h₆
          field_simp
          linarith
        -- Plug it into h₅ to get f(x) = x(x+t+1/tx)(1-t/x) = x² - 1/x - (t² - 1/t).
        replace h₇ : (f x - (x ^ 2 - 1 / x - (t ^ 2 - 1 / t))) * (f x * x * t) = 0 := by
          rw [h₇] at h₅
          field_simp at h₅ ⊢
          linarith
        simp [ht₀, hx, this, -one_div] at h₇
        -- However, note that f(x) = x² - 1/x by a previous lemma, which implies that t² - 1/t = 0.
        have h₈ := h₂ x hx
        simp [this, -one_div] at h₈
        replace h₇ : t ^ 2 - 1 / t = 0 := by
          linarith
        -- Now t³ = 1³, and t is a real number, so t = 1.
        replace h₇ : (t - 1) * ((t + 1 / 2) ^ 2 + 3 / 4) = 0 := by
          field_simp at h₇
          linarith
        simp [show (t + 1 / 2) ^ 2 + 3 / 4 ≠ 0 by positivity, -one_div] at h₇
        -- A contradiction is derived, since we assume that t ≠ 0.
        absurd ht₁
        linarith only [h₇]
      -- We get the goal that f(x) = 0 ∀ x ≠ 0.
      exact h₄
  . -- Now show that the two solutions satisfy the condition.
    intro hf
    obtain hf | hf := hf
    . -- Suppose f(x) = 0 ∀ x ≠ 0.
      intro x y z hxyz
      simp [hf x (by by_contra!; simp [this] at hxyz), hf y (by by_contra!; simp [this] at hxyz), hf z (by by_contra!; simp [this] at hxyz)]
    . -- Suppose f(x) = x² - 1/x.
      intro x y z hxyz
      have hnzero : ¬(x = 0 ∨ y = 0 ∨ z = 0) := by
        by_contra!
        obtain h | h | h := this
        all_goals
          simp [h] at hxyz
      simp at hnzero
      simp [hf x hnzero.1, hf y hnzero.2.1, hf z hnzero.2.2, -one_div]
      -- Field simp does not work well here.
      -- Now the goal is to show that (x² - 1 / x)² - (y² - 1 / y)(z² - 1 / z) = x(x + y + z)(x² - 1 / x + y² - 1 / y + z² - 1 / z).
      calc
        (x ^ 2 - 1 / x) ^ 2 - (y ^ 2 - 1 / y) * (z ^ 2 - 1 / z)
        _ = x ^ 4 - 2 * x + ((x * y * z) / x) ^ 2 - (y * z) ^ 2 + z ^ 2 / y + y ^ 2 / z - (x * y * z) / (y * z) := by
          -- Use the fact that xyz = 1.
          rw [hxyz, sub_sq, sub_mul, mul_sub, mul_sub, show 2 * x ^ 2 * (1 / x) = 2 * x by field_simp [hnzero.1]; ring]
          ring
        _ = x * (x ^ 3 - 3 + z ^ 3 + y ^ 3) := by
          -- Further simplify the expression.
          rw [mul_add, mul_add, mul_sub, mul_assoc x y z, mul_div_cancel_left₀ _ hnzero.1, mul_div_cancel_right₀ _ (by simp [hnzero.2])]
          have g₀ : x * z ^ 3 = z ^ 2 / y := by
            field_simp [hnzero.2.1]
            calc
              x * z ^ 3 * y = z ^ 2 * (x * y * z) := by ring
              _ = z ^ 2 := by simp [hxyz]
          have g₁ : x * y ^ 3 = y ^ 2 / z := by
            field_simp [hnzero.2.2]
            calc
              x * y ^ 3 * z = y ^ 2 * (x * y * z) := by ring
              _ = y ^ 2 := by simp [hxyz]
          rw [<-g₀, <-g₁]
          ring
        _ = x * (x + y + z) * (x ^ 2 - 1 / x + y ^ 2 - 1 / y + z ^ 2 - 1 / z) := by
          -- Cancel x of both sides.
          rw [mul_assoc, mul_eq_mul_left_iff]
          simp [hnzero.1, -one_div]
          rw [mul_sub, mul_add, mul_sub, mul_add, mul_sub]
          iterate 12 rw [add_mul]
          -- Simplify the expression using xyz = 1.
          repeat rw [mul_one_div]
          rw [div_self hnzero.1, div_self hnzero.2.1, div_self hnzero.2.2]
          have g₀ : z * y ^ 2 = y / x := by
            field_simp [hnzero.1]
            calc
              z * y ^ 2 * x = y * (x * y * z) := by ring
              _ = y := by simp [hxyz]
          have g₁ : y * z ^ 2 = z / x := by
            field_simp [hnzero.1]
            calc
              y * z ^ 2 * x = z * (x * y * z) := by ring
              _ = z := by simp [hxyz]
          have g₂ : z * x ^ 2 = x / y := by
            field_simp [hnzero.2.1]
            calc
              z * x ^ 2 * y = x * (x * y * z) := by ring
              _ = x := by simp [hxyz]
          have g₃ : x * z ^ 2 = z / y := by
            field_simp [hnzero.2.1]
            calc
              x * z ^ 2 * y = z * (x * y * z) := by ring
              _ = z := by simp [hxyz]
          have g₄ : y * x ^ 2 = x / z := by
            field_simp [hnzero.2.2]
            calc
              y * x ^ 2 * z = x * (x * y * z) := by ring
              _ = x := by simp [hxyz]
          have g₅ : x * y ^ 2 = y / z := by
            field_simp [hnzero.2.2]
            calc
              x * y ^ 2 * z = y * (x * y * z) := by ring
              _ = y := by simp [hxyz]
          rw [<-g₀, <-g₁, <-g₂, <-g₃, <-g₄, <-g₅]
          ring
        _ = x * (x + y + z) * (x ^ 2 - 1 / x + (y ^ 2 - 1 / y) + (z ^ 2 - 1 / z)) := by
          ring