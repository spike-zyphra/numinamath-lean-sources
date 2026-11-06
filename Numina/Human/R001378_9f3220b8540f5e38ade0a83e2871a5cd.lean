import Mathlib

/- BLR   Let $f$ be any function that maps the set of real numbers into the set of real numbers. Prove that there exist real numbers $x$ and $y$ such that  $$ f(x-f(y))>y f(x)+x $$ -/
theorem algebra_23804 (f : ℝ → ℝ) : ∃ x y, f (x - f y) > y * f x + x := by
  -- Proof by contradiction.
  by_contra! hf
  -- Let a = f(0).
  let a := f 0
  -- Substitute y = 0 in the hypothesis.
  have h₀ (x : ℝ) : f (x - a) ≤ x := by
    specialize hf x 0
    simp [a]
    rw [zero_mul, zero_add] at hf
    exact hf
  replace h₀ (y : ℝ) : f y ≤ y + a := by
    specialize h₀ (y + a)
    rw [add_sub_cancel_right] at h₀
    exact h₀
  -- Substitute x = f(y) in hf.
  have h₁ (y : ℝ) : a ≤ y * f (f y) + (y + a) := by
    specialize hf (f y) y
    simp [a] at h₀ ⊢
    rw [sub_self] at hf
    linarith only [h₀ y, hf]
  replace h₁ (y : ℝ) : y * (f (f y) + 1) ≥ 0 := by
    linarith only [h₁ y]
  -- We have f(f(y)) ≥ -1 for all positive y.
  have h₂ (y : ℝ) (ypos : 0 < y) : f (f y) + 1 ≥ 0 := by
    specialize h₁ y
    rw [show 0 = y * 0 by simp] at h₁
    exact le_of_mul_le_mul_left h₁ ypos
  -- We have f(y) ≥ -a - 1 for all positive y.
  have h₃ (y : ℝ) (ypos : 0 < y) : f y ≥ -a - 1 := by
    simp [a]
    linarith only [h₀ (f y), h₂ y ypos]
  -- We have f(x) ≤ 0 for all x.
  have h₄ : ∀ x, f x ≤ 0 := by
    by_contra!
    obtain ⟨x₀, hx₀⟩ := this
    let y₀ := min (x₀ - a) ((-a - x₀ - 1) / f x₀) - 1
    have hx₁ : y₀ < x₀ - a := by
      calc
        y₀ ≤ x₀ - a - 1 := by simp [y₀]
        _ < x₀ - a := by simp
    have hx₂ : y₀ < (-a - x₀ - 1) / f x₀ := by
      calc
        y₀ ≤ (-a - x₀ - 1) / f x₀ - 1 := by simp [y₀]
        _ < (-a - x₀ - 1) / f x₀ := by simp
    rw [lt_div_iff hx₀] at hx₂
    have hx₃ : x₀ - f y₀ > 0 := by
      calc
        x₀ - f y₀ ≥ x₀ - (y₀ + a) := by linarith only [h₀ y₀]
        _ > 0 := by linarith only [hx₁]
    have hx₄ : y₀ * f x₀ + x₀ ≥ -a - 1 := by
      calc
        y₀ * f x₀ + x₀ ≥ f (x₀ - f y₀) := by exact hf x₀ y₀
        _ ≥ -a - 1 := by exact h₃ (x₀ - f y₀) hx₃
    -- Derive a contradiction from hx₂ and hx₄.
    linarith only [hx₂, hx₄]
  replace h₀ (y : ℝ) : f y ≤ y := by
    linarith only [h₀ y, h₄ 0]
  let y₀ := max 1 (-f (-1))
  have hy₀ : y₀ > -f (-1) - 1 := by
    simp [y₀]
  let x₀ := f y₀ - 1
  have hy₁ : f (-1) ≤ -y₀ - 1 := by
    calc
      f (-1) = f (x₀ - f y₀) := by simp [x₀]
      _ ≤ y₀ * f x₀ + x₀ := hf x₀ y₀
      _ = y₀ * f (f y₀ - 1) + (f y₀ - 1) := by simp [x₀]
      _ ≤ y₀ * (f y₀ - 1) - 1 := by linarith only [show y₀ * f (f y₀ - 1) ≤ y₀ * (f y₀ - 1) by simp [show 0 < y₀ by simp [y₀]]; exact h₀ (f y₀ - 1), h₄ y₀]
      _ ≤ -y₀ - 1 := by linarith only [show y₀ * f y₀ ≤ 0 by nlinarith only [show 0 < y₀ by simp [y₀], h₄ y₀]]
  -- Derive a contradiction from hy₀ and hy₁.
  linarith only [hy₀, hy₁]
