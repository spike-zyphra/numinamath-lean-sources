import Mathlib

/- Let $a_{0}, a_{1}, \ldots, a_{N}$ be real numbers satisfying $a_{0}=a_{N}=0$ and

$$
a_{i+1}-2 a_{i}+a_{i-1}=a_{i}^{2}
$$

for $i=1,2, \ldots, N-1$. Prove that $a_{i} \leqslant 0$ for $i=1,2, \ldots, N-1$. -/
theorem number_theory_238069 (N : ℕ) (a : Fin (N + 1) → ℝ) (h₀ : a 0 = 0) (h₁ : a N = 0) (h₂ : ∀ i : ℕ, 0 < i → i < N → a (i + 1) - 2 * a i + a (i - 1) = a i ^ 2) :
    ∀ i : ℕ, 0 < i → i < N → a i ≤ 0 := by
  -- Let x be the maximum value of a.
  let x := Finset.max' (Finset.image a Finset.univ) (by simp)
  -- Let i be the index of x.
  obtain ⟨i, hi⟩ : ∃ i, a i = x := by
    have h : x ∈ Finset.image a Finset.univ := Finset.max'_mem _ _
    simp at h
    exact h
  -- By definition, a j ≤ x for all j.
  have h₃ (j : Fin (N + 1)) : a j ≤ x := Finset.le_max' _ _ (by simp)
  -- It suffices to show that x ≤ 0.
  suffices H : x ≤ 0 by
    -- If the statement is false
    by_contra! K
    -- Then there exists some 0 < j < N such that a j > 0.
    rcases K with ⟨j, hj₁, hj₂, hj₃⟩
    -- Then x ≥ a j > 0.
    specialize h₃ j
    linarith
  -- We show x ≤ 0 by contradiction, supposing x > 0.
  by_contra! K
  -- As a 0 = a N = 0, we have 0 < i < N.
  have hi₁ : 0 < i := by
    by_contra! s
    simp at s
    simp [s, h₀] at hi
    simp [hi] at K
  have hi₂ : i < N := by
    by_contra! s
    simp at s h₁
    simp [s, h₁] at hi
    simp [hi] at K
  -- We have a (i - 1) ≤ a i and a (i + 1) ≤ a i.
  have h₄ := h₃ (i - 1)
  have h₅ := h₃ (i + 1)
  rw [← hi] at h₄ h₅ K
  -- And by definition, a i ^ 2 = a (i + 1) - 2 * a i + a (i - 1).
  specialize h₂ i hi₁ (by simp at hi₂; norm_cast)
  simp at h₂
  -- We can now derive 0 < 0, a contradiction.
  have contra : (0 : ℝ) < 0 := by
    calc
      -- 0 < a i ^ 2 because a i > 0
      0 < a i ^ 2 := sq_pos_of_pos K
      -- ... = a (i + 1) - 2 * a i + a (i - 1)
      _ = a (i + 1) - 2 * a i + a (i - 1) := by rw [h₂]
      -- ... = (a (i + 1) - a i) + (a i - a (i - 1)) ≤ 0
      _ ≤ 0 := by linarith only [h₄, h₅]
  simp at contra
