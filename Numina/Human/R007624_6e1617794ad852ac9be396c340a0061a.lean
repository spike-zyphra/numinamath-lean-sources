import Mathlib

/- Let $\mathbf{R}$ denote the set of all real numbers. Find all functions $f: \mathbf{R} \rightarrow \mathbf{R}$ satisfying the condition

$$
f(x+y)=f(x) f(y) f(x y)
$$

for all $x, y$ in $\mathbf{R}$. -/
theorem algebra_607796 :
  {f : ℝ → ℝ | ∀ x y, f (x + y) = f x * f y * f (x * y)} = {0, 1, -1} := by
  ext f
  simp
  constructor
  -- First, we verify that 0, 1, and -1 are indeed solutions.
  swap
  . rintro (rfl | rfl | rfl)
    all_goals
      simp
  -- Now, we show that these are the only solutions.
  . intro H
    -- First, we show that f(0) must be 0, 1, or -1.
    have h₀ : f 0 = f 0 * f 0 * f 0 := by
      specialize H 0 0
      simp at H
      exact H
    replace h₀ : f 0 * (f 0 - 1) * (f 0 + 1) = 0 := by linear_combination -h₀
    simp at h₀
    -- Consider the cases one by one.
    rcases h₀ with ((h₀ | h₀) | h₀)
    . -- If f(0) = 0, then f(x) = 0 for all x by setting y = 0 in the given functional equation.
      left
      ext x
      simp
      specialize H x 0
      simp [h₀] at H
      exact H
    . -- If f(0) = 1
      right; left
      replace h₀ : f 0 = 1 := by linear_combination h₀
      -- Setting y = -x, we get 1 = f(x) * f(-x) * f(-x^2)
      have h₁ x := H x (-x)
      simp [h₀] at h₁
      -- This implies f(x) ≠ 0 for all x.
      have h₂ x : f x ≠ 0 := by
        intro h
        specialize h₁ x
        simp [h] at h₁
      -- Setting x = 1 and y = x - 1, we get f(x) = f(1) * f(x - 1) ^ 2
      have h₃ x := H 1 (x - 1)
      simp at h₃
      have h₄ x : f x = f x * (f 1 * f (-1) ^ 2 * f x * f (-x) ^ 2) := by
        specialize h₃ x
        calc f x
          _ = f 1 * f (x - 1) * f (x - 1) := h₃
          _ = f 1 * f (x + (-1)) ^ 2 := by ring_nf
          -- And we further use the given functional equation for f(x + (-1))
          _ = f 1 * (f x * f (-1) * f (x * (-1))) ^ 2 := by rw [H x (-1)]
          _ = f x * (f 1 * f (-1) ^ 2 * f x * f (-x) ^ 2) := by ring_nf
      -- By cancelling the f(x) on both sides, we get k * (f(x) * f(-x)^2) = 1 for all x, where k = f(1) * f(-1)^2
      simp [h₂] at h₄
      obtain ⟨k, h₅⟩ : ∃ k, ∀ x, k * (f x * f (-x) ^ 2) = 1 := by
        use f 1 * f (-1) ^ 2
        intro x
        linear_combination h₄ x
      -- Now we replace x with -x in the above equation and we get k * (f(-x) * f(x)^2) = 1 for all x
      -- It tells us that f(-x) = f(x) for all x
      have h₆ x : f (-x) = f x := by
        have h₆ := h₅ x
        have h₇ := h₅ (-x)
        simp at h₇
        have h₈ : f x * f (-x) ^ 2 = f (-x) * f x ^ 2 := by
          calc f x * f (-x) ^ 2
            _ = f x * f (-x) ^ 2 * (k * (f (-x) * f x ^ 2)) := by simp [h₇]
            _ = (k * (f x * f (-x) ^ 2)) * (f (-x) * f x ^ 2) := by ring
            _ = f (-x) * f x ^ 2 := by simp [h₆]
        replace h₈ : f x * f (-x) * f (-x) = f x * f (-x) * f x := by linear_combination h₈
        simp [h₂] at h₈
        exact h₈
      -- Now we have k * f(x)^3 = 1 for all x
      simp [h₆] at h₅
      -- So k = 1 and f(x) = 1 for all x
      obtain rfl : k = 1 := by
        specialize h₅ 0
        simp [h₀] at h₅
        exact h₅
      replace h₅ x : f x ^ 3 = 1 ^ 3 := by linear_combination h₅ x
      ext x
      simp
      specialize h₅ x
      rw [pow_eq_pow_iff_of_ne_zero (by simp)] at h₅
      simp [show ¬ Even 3 from Nat.not_even_iff.mpr rfl] at h₅
      exact h₅
    . -- The same argument works for f(0) = -1
      right; right
      replace h₀ : f 0 = -1 := by linear_combination h₀
      have h₁ x := H x (-x)
      simp [h₀] at h₁
      have h₂ x : f x ≠ 0 := by
        intro h
        specialize h₁ x
        simp [h] at h₁
      have h₃ x := H 1 (x - 1)
      simp at h₃
      have h₄ x : f x = f x * (f 1 * f (-1) ^ 2 * f x * f (-x) ^ 2) := by
        specialize h₃ x
        calc f x
          _ = f 1 * f (x - 1) * f (x - 1) := h₃
          _ = f 1 * f (x + (-1)) ^ 2 := by ring_nf
          _ = f 1 * (f x * f (-1) * f (x * (-1))) ^ 2 := by rw [H x (-1)]
          _ = f x * (f 1 * f (-1) ^ 2 * f x * f (-x) ^ 2) := by ring_nf
      simp [h₂] at h₄
      obtain ⟨k, h₅⟩ : ∃ k, ∀ x, k * (f x * f (-x) ^ 2) = 1 := by
        use f 1 * f (-1) ^ 2
        intro x
        linear_combination h₄ x
      have h₆ x : f (-x) = f x := by
        have h₆ := h₅ x
        have h₇ := h₅ (-x)
        simp at h₇
        have h₈ : f x * f (-x) ^ 2 = f (-x) * f x ^ 2 := by
          calc f x * f (-x) ^ 2
            _ = f x * f (-x) ^ 2 * (k * (f (-x) * f x ^ 2)) := by simp [h₇]
            _ = (k * (f x * f (-x) ^ 2)) * (f (-x) * f x ^ 2) := by ring
            _ = f (-x) * f x ^ 2 := by simp [h₆]
        replace h₈ : f x * f (-x) * f (-x) = f x * f (-x) * f x := by linear_combination h₈
        simp [h₂] at h₈
        exact h₈
      simp [h₆] at h₅
      obtain rfl : k = -1 := by
        specialize h₅ 0
        simp [h₀] at h₅
        linear_combination -h₅
      replace h₅ x : f x ^ 3 = (-1) ^ 3 := by linear_combination -h₅ x
      ext x
      simp
      specialize h₅ x
      rw [pow_eq_pow_iff_of_ne_zero (by simp)] at h₅
      simp [show ¬ Even 3 from Nat.not_even_iff.mpr rfl] at h₅
      exact h₅
