import Mathlib

/- Vind alle functies $f: \mathbb{Z} \rightarrow \mathbb{Z}$ die voldoen aan

$$
f(-f(x)-f(y))=1-x-y
$$

voor alle $x, y \in \mathbb{Z}$. -/
theorem algebra_604872 :
    {f : ℤ → ℤ | ∀ x y, f (-f x - f y) = 1 - x - y} = {fun x => x - 1} := by
  -- Split the goal into two parts.
  ext f
  simp
  apply Iff.intro
  . -- First show that the condition implies the solution f(x) = x - 1.
    intro h₀
    -- Set x = y = 1 into the condition.
    have h₁ : f (-f 1 - f 1) = 1 - 1 - 1 := by
      apply h₀
    -- Set x = n, y = 1 into the condition.
    have h₂ (n : ℤ) : f (-f n - f 1) = 1 - n - 1 := by
      apply h₀
    -- Set x = -f(n) - f(1), y = -f(1) - f(1), we get f(n + 1) = f(n) + (3f(1) + 1).
    have h₃ (n : ℤ) : f (n + 1) = f n + 3 * f 1 + 1 := by
      specialize h₀ (-f n - f 1) (-f 1 - f 1)
      rw [h₂, h₁] at h₀
      ring_nf at h₀ ⊢
      linarith only [h₀]
    -- Let c = 3f(1) + 1.
    let c := 3 * f 1 + 1
    -- We have f(n + 1) = f(n) + c.
    replace h₃ (n : ℤ) : f (n + 1) = f n + c := by
      simp [c]
      rw [<-add_assoc]
      exact h₃ n
    -- We have f(n) = f(0) + cn for all n. We prove this by induction.
    have h₄ (n : ℕ) : f n = f 0 + c * n ∧ f (-n) = f 0 - c * n := by
      induction n with
      | zero =>
        simp [h₃]
      | succ n hn =>
        refine ⟨?_, ?_⟩
        . simp [h₃, hn.1]
          ring
        . specialize h₃ (-n - 1)
          simp [hn.2] at h₃
          rw [add_comm]
          simp
          rw [<-sub_eq_add_neg]
          linarith only [h₃]
    replace h₄ (n : ℤ) : f n = f 0 + c * n := by
      by_cases hn : n ≥ 0
      . specialize h₄ (n.natAbs)
        zify at h₄
        simp [abs_of_nonneg hn] at h₄
        exact h₄.1
      . replace h₄ := (h₄ (-n).natAbs).2
        zify at h₄
        simp [abs_of_nonpos (show n ≤ 0 by linarith)] at h₄
        exact h₄
    -- Let d = f(0).
    let d := f 0
    -- Now f(n) = cn + d for all n.
    rw [show f 0 = d by rfl] at h₄
    -- Substitute h₄ into the original equation and simplify.
    have h₅ (x y : ℤ) : 1 - x - y = (d - 2 * c * d) - c ^ 2 * x - c ^ 2 * y := by
      rw [<-h₀, h₄, h₄, h₄]
      ring
    -- Do some substitutions with one of the variables fixed to show that the coefficients on both sides agree.
    have g₀ := h₅ 0 0
    -- We get d - 2cd = 1.
    simp at g₀
    rw [<-g₀] at h₅
    have g₁ := h₅ 0 1
    -- We get 1 - c² = 1.
    simp at g₁
    rw [show (1 : ℤ) = 1 ^ 2 by norm_num, sq_sub_sq] at g₁
    simp at g₁
    cases g₁ with
    | inl g₁ =>
      -- If 1 + c = 0, contradictory to g₀ because it means 3d = 1.
      omega
    | inr g₁ =>
      replace g₁ : c = 1 := by
        omega
      replace g₀ : d = -1 := by
        rw [g₁] at g₀
        omega
      ext n
      rw [g₀, g₁] at h₄
      specialize h₄ n
      linarith only [h₄]
  . -- Now show that f(x) = x - 1 satisfies the condition.
    intro h₀ x y
    simp [h₀]
    ring
