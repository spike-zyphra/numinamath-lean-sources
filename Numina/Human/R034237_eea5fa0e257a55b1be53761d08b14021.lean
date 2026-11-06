import Mathlib

/- $a$, $b$, and $c$ are three positive integers. If $a + b + c = abc = m$, find the value of $m$. -/
theorem number_theory_629264 (a b c m : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h₁ : a + b + c = m) (h₂ : a * b * c = m) :
    m = 6 := by
  -- By symmetry, we may assume a <= b <= c.
  wlog h₃ : a ≤ b ∧ b ≤ c with H
  {
    -- We can use `Tuple.sort` to sort the numbers.
    let f := ![a, b, c]
    let σ := Tuple.sort f
    -- Each number of `f` is positive.
    have h₄ (i : Fin 3) : 0 < f i := by
      fin_cases i
      . simp [f, ha]
      . simp [f, hb]
      . simp [f, hc]
    -- We set a' := f (σ 0), b' := f (σ 1), c' := f (σ 2).
    let a' := f (σ 0)
    let b' := f (σ 1)
    let c' := f (σ 2)
    -- We have a' + b' + c' = m.
    have h₅ : a' + b' + c' = m := by
      -- We have a' + b' + c' = ∑ i, f (σ i).
      have h₅ : a' + b' + c' = ∑ i, f (σ i) := by
        simp [a', b', c', Finset.sum]
        ring
      -- We have ∑ i, f (σ i) = ∑ i, f i.
      rw [Equiv.Perm.sum_comp _ _ _ (by simp)] at h₅
      simp [Finset.sum, f] at h₅
      linarith only [h₁, h₅]
    -- The same argument shows that a' * b' * c' = m.
    have h₆ : a' * b' * c' = m := by
      have h₆ : a' * b' * c' = ∏ i, f (σ i) := by
        simp [a', b', c', Finset.prod]
        ring
      rw [Equiv.Perm.prod_comp _ _ _ (by simp)] at h₆
      simp [Finset.prod, f] at h₆
      linarith only [h₂, h₆]
    -- We have a' ≤ b' ≤ c' since `f` is sorted.
    have h₇ : a' ≤ b' ∧ b' ≤ c' := by
      have h₇ := Tuple.monotone_sort f
      exact ⟨by simpa using h₇ (show 0 ≤ 1 by simp), by simpa using h₇ (show 1 ≤ 2 by simp)⟩
    -- We can now apply the `wlog` hypothesis.
    exact H a' b' c' m (h₄ _) (h₄ _) (h₄ _) h₅ h₆ h₇
  }
  -- abc = a + b + c ≤ 3c, so a * b ≤ 3.
  have h₄ : a * b ≤ 3 := by nlinarith
  -- Since a ≤ b, so a < 2.
  have h₅ : a < 2 := by nlinarith
  -- So a = 1.
  interval_cases a
  -- So b = 1, 2 or 3, we can check each case.
  simp at h₄
  interval_cases b <;> omega
