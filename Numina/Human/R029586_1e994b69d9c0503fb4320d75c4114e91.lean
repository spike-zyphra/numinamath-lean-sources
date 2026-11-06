import Mathlib

/-Determine all functions $f: \mathbb{Z} \rightarrow \mathbb{Z}$ with the property that  $$ f(x-f(y))=f(f(x))-f(y)-1 $$  holds for all $x, y \in \mathbb{Z}$. (Croatia)-/
theorem algebra_24551 (f : ℤ → ℤ) : (∀ x y : ℤ, f (x - f y) = f (f x) - f y - 1) ↔ (∀ x : ℤ, f x = -1) ∨ (∀ x : ℤ, f x = x + 1) := by
  -- Divide the proof into two parts.
  apply Iff.intro <;> intro h
  -- show that f(x) = -1 or f(x) = x + 1, ∀x ∈ ℤ.
  . -- Substitute (x, y) = (0, f(0)).
    -- so that we have f (-f (f 0)) = -1
    have h1 := h 0 (f 0)
    simp at h1
    -- Substitute (x, y) = (x, -f(f(0)))
    -- show that f (x + 1) = f (f x)
    have h2 (x : ℤ) : f (x + 1) = f (f x) := by
      have h2 := h x (-f (f 0))
      rw [h1] at h2
      simp at h2
      exact h2
    -- show that f(x - f y) = f(x + 1) - f y - 1
    replace h (x y : ℤ) : f (x - f y) = f (x + 1) - f y - 1 := by
      rw [h2 x]
      apply h
    -- show that f (x + 1) = f x + (f (-1) + 1)
    have h3 (x : ℤ) : f (x + 1) = f x + (f (-1) + 1) := by
      -- calculate f(x + 1) - f x
      have h3 (x : ℤ) : f (x + 1) - f x = f (-1) + 1 := by
        calc
          f (x + 1) - f x = f (x + 1) - f x - 1 + 1 := by ring_nf
          _ = f (x - f x) + 1 := by rw [h]
          _ = f (x - 1 - f x + 1) + 1 := by ring_nf
          _ = f (f (x - 1 - f x)) + 1 := by rw [h2]
          _ = f (-1) + 1 := by rw [h]; ring_nf
      linarith only [h3 x]
    -- Set A = f(-1) + 1, B = f 0
    set A : ℤ := f (-1) + 1 with hA
    set B : ℤ := f 0 with hB
    -- finally show that f x = A * x + B
    replace h3 (x : ℤ) : f x = A * x + B := by
      -- use the induction of int
      induction' x using Int.induction_on with x hx x hx
      -- when x = 0
      . simp
      -- when x satisfied, show the case of x + 1
      . simp at hx ⊢
        rw [h3, hx]
        ring_nf
      -- when -x satisfied, show the case of -x - 1
      . simp at hx ⊢
        replace h3 := h3 (-(x : ℤ) - 1)
        simp at h3
        linarith only [h3, hx]
      
    -- Substitute f x = A * x + B into h2.
    replace h2 (x : ℤ) : A * (x + 1) + B = A * (A * x + B) + B := by
      have h2 := h2 x
      rw [h3, h3, h3] at h2
      linarith only [h2]
    -- Substitute x = 1 into h2.
    have h4 := h2 1
    simp at h4
    have h2 := h2 0
    simp at h2
    cases h4 with
    | inr h4 => -- Suppose A = 0.
      rw [h4] at h3
      rw [hA] at h4
      have h5 := h3 (-1)
      have h6 : B = -1 := by
        linarith only [h4, h5]
      simp [h6] at h3
      -- We have f(x) = -1 for all x ∈ ℤ.
      left
      exact h3
    | inl h4 => -- Suppose A ≠ 0, then 2 = A + B.
      replace h4 : B = 2 - A := by linarith only [h4]
      rw [h4] at h2
      replace h2 : A * (A - 1) = 0 := by linarith only [h2]
      replace h2 : A = 0 ∨ A - 1 = 0 := by rw [Int.mul_eq_zero] at h2; tauto
      -- We have f(x) = 1 for all x ∈ ℤ.
      cases h2 with
      | inr h2 => -- when A = 0
        right
        simp [show A = 1 by linarith only [h2], show B = 1 by linarith only [h2, h4]] at h3
        exact h3
      | inl h2 => -- when A = 1
        simp [show A = 0 by linarith only [h2]] at h3
        rw [h3] at hA
        linarith only [h2, hA, h4]
  -- show that f(x) = -1 or f(x) = x + 1 is the answer.
  . obtain h | h := h
    . intro x y
      simp [h]
    . intro x y
      simp [h]
      ring_nf
      