import Mathlib

/- Determine all functions $f: \mathbb{Z} \rightarrow \mathbb{Z}$ with the property that  $$ f(x-f(y))=f(f(x))-f(y)-1 $$  holds for all $x, y \in \mathbb{Z}$. (Croatia) Answer. There are two such functions, namely the constant function $x \mapsto-1$ and the successor function $x \mapsto x+1$. -/
theorem algebra_24668 (f : ℤ → ℤ) : (∀ x y : ℤ, f (x - f y) = f (f x) - f y - 1) ↔ (∀ x : ℤ, f x = -1) ∨ (∀ x : ℤ, f x = x + 1) := by
  -- Break the iff into two implications.
  apply Iff.intro <;> intro h₀
  . -- If f(x - f(y)) = f(f(x)) - f(y) - 1 for all x, y ∈ ℤ, then f(x) = -1 or f(x) = x + 1 for all x ∈ ℤ.
    -- Substitute (x, y) = (0, f(0)) into h₀.
    have h₁ := h₀ 0 (f 0)
    simp at h₁
    -- Substitute (x, y) = (x, -f(f(0))) into h₀.
    have h₂ (x : ℤ) : f (x + 1) = f (f x) := by
      specialize h₀ x (-f (f 0))
      rw [h₁] at h₀
      simp at h₀
      exact h₀
    replace h₀ (x y : ℤ) : f (x - f y) = f (x + 1) - f y - 1 := by
      rw [h₂ x]
      apply h₀
    -- Compute f(x + 1) - f(x).
    have h₃ (x : ℤ) : f (x + 1) = f x + (f (-1) + 1) := by
      calc
        f (x + 1) = f (x + 1) - f x - 1 + f x + 1 := by ring_nf
        _ = f (x - f x) + f x + 1 := by rw [h₀]
        _ = f ((x - 1 - f x) + 1) + f x + 1 := by ring_nf
        _ = f (f (x - 1 - f x)) + f x + 1 := by rw [h₂]
        _ = f x + (f (-1) + 1) := by rw [h₀]; ring_nf
    -- Show that f is linear.
    let A : ℤ := f (-1) + 1
    let B : ℤ := f 0
    replace h₃ (x : ℕ) : f x = A * x + B ∧ f (-x : ℤ) = A * (-x : ℤ) + B := by
      -- Perform induction on x.
      induction x with
      | zero =>
        simp
      | succ x hx =>
        refine ⟨?_, ?_⟩
        . zify
          rw [h₃, hx.1]
          ring_nf
        . zify
          calc
            f (-(x + 1 : ℤ)) = f (-(x + 1 : ℤ)) + (f (-1) + 1) - A := by dsimp [A]; ring_nf
            _ = f (-(x + 1 : ℤ) + 1) - A := by rw [<-h₃]
            _ = A * (-(x + 1 : ℤ)) + B := by simp; rw [hx.2]; ring_nf
    replace h₃ (x : ℤ) : f x = A * x + B := by
      have h₄ : x = x.natAbs ∨ x = -x.natAbs := Int.natAbs_eq x
      cases h₄ with
      | inl h₄ =>
        replace h₃ := (h₃ (x.natAbs)).1
        rw [<-h₄] at h₃
        exact h₃
      | inr h₄ =>
        replace h₃ := (h₃ (x.natAbs)).2
        rw [<-h₄] at h₃
        exact h₃
    -- Substitute this new relation into h₂.
    conv at h₂ =>
      intro x
      rw [h₃, h₃, h₃]
    -- Substitute x = 1 into h₂.
    have h₄ := h₂ 1
    simp at h₄
    by_cases h₅ : A = 0
    . -- Suppose A = 0.
      rw [h₅] at h₃
      dsimp [A] at h₅
      have h₆ := h₃ (-1)
      have h₇ : B = -1 := by
        linarith only [h₅, h₆]
      simp [h₇] at h₃
      -- We have f(x) = -1 for all x ∈ ℤ.
      left
      exact h₃
    . -- Suppose A ≠ 0, then 2 = A + B.
      simp [h₅] at h₄
      specialize h₂ 0
      simp at h₂
      simp [h₅] at h₂
      rw [h₂] at h₄
      simp [show A = 1 by linarith only [h₄], h₂] at h₃
      -- We have f(x) = 1 for all x ∈ ℤ.
      right
      exact h₃
  . -- If f(x) = -1 or f(x) = x + 1 for all x ∈ ℤ, then f(x - f(y)) = f(f(x)) - f(y) - 1 for all x, y ∈ ℤ.
    obtain h | h := h₀
    . intro x y
      simp [h]
    . intro x y
      simp [h]
      ring_nf
        
