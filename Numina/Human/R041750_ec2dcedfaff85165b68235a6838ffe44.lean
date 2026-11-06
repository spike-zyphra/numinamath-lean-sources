import Mathlib

/-Given that $f(x) = x^k$ where $k < 0$, what is the range of $f(x)$ on the interval $[1, \infty)$?-/
theorem algebra_10339 (f : ℝ → ℝ) (k : ℝ) (hk : k < 0) (hf : ∀ x, f x = x ^ k) :
    Set.Ioc 0 1 = f ''Set.Ici 1 := by
  -- simplify the set form
  ext x
  simp
  apply Iff.intro <;> intro h
  -- show that ∀ 1 ≤ x, x ∈ Im (f)
  . use (x ^ k⁻¹) -- exact f (x ^ k⁻¹) = x
    refine ⟨?_, ?_⟩
    -- verify the range of x ^ k⁻¹
    . have eq₁ : (1 : ℝ) ^ k⁻¹ = 1 := by
        rw [Real.one_rpow]
      rw [<-eq₁]
      apply Real.rpow_le_rpow_of_exponent_nonpos
      tauto
      tauto
      rw [inv_nonpos]
      linarith only [hk]
    -- verify f (x ^ k⁻¹) = x
    . rw [hf]
      rw [Real.rpow_inv_rpow]
      linarith only [h]
      linarith only [hk]
  -- show that f([1, ∞)) = (0, 1]
  . obtain ⟨y, hy, hfy⟩ := h
    refine ⟨?_, ?_⟩
    . rw [hf] at hfy
      rw [<-hfy]
      apply Real.rpow_pos_of_pos
      linarith only [hy]
    . rw [<-hfy]
      rw [hf]
      apply Real.rpow_le_one_of_one_le_of_nonpos
      exact hy
      linarith only [hk]