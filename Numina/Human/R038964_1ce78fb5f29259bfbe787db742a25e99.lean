import Mathlib

/- 17. For the numbers $a_{0}, a_{1}, a_{2}, \ldots, a_{n-1}, a_{n}$, it is known that $a_{0}=a_{n}=0$ and that $a_{k-1}-2 a_{k}+a_{k+1} \geqslant 0$ for all $k(k=1,2,3, \ldots, n-1)$. Prove that all numbers $a$ are non-positive. -/
theorem inequalities_190008 (n : ℕ) (a : ℕ → ℝ)
    (h₀ : a 0 = 0) (h₁ : a n = 0)
    (h₂ : ∀ k, k + 2 ≤ n →  a k - 2 * a (k + 1) + a (k + 2) ≥ 0) :
    ∀ i ∈ Finset.Icc 0 n, a i ≤ 0 := by
  -- first we convert the condition to that of relation between subtractions
  replace h₂ (k : ℕ) (hk : k + 2 ≤ n) : a (k + 1) - a k ≤ a (k + 2) - a (k + 1) := by
    specialize h₂ k hk
    linarith
  -- we'll prove by contradiction, assume there are positive a r
  by_contra h
  push_neg at h
  -- take the minimum such r, prove let's prove it's properties that wil be useful
  obtain ⟨hr1, hr2⟩ := Nat.find_spec h
  have hr3 (m : ℕ) := Nat.find_min h (m := m)
  set r := Nat.find h with hr
  -- next prove 0 < r, as 0 = r can't happen due to a 0 = 0
  have hr4 : 0 < r := by
    apply Nat.pos_iff_ne_zero.mpr
    rintro h'
    simp [h', h₀] at hr2
  -- so a(r-1) must be non-positive
  specialize hr3 (r - 1) (by omega)
  push_neg at hr3
  have hr5 : a (r - 1) ≤ 0 := by
    apply hr3
    simp at hr1 ⊢
    linarith
  -- now use induction to prove a(k+1) - a(k) > 0 for k >= r-1 using the condition and since a(r) > 0, a(r-1) <= 0
  have hr6 (k : ℕ) (hk : r - 1 ≤ k) (hk' : k + 1 ≤ n) : 0 < a (k + 1) - a k := by
    induction' k, hk using Nat.le_induction with m hm hm'
    . rw [show r - 1 + 1 = r by omega]
      linarith
    . calc
        _ < a (m + 1) - a m := by
          apply hm'
          linarith
        _ ≤ a (m + 1 + 1) - a (m + 1) := by
          apply h₂
          linarith
  -- prove r < n as r = n can't happen due to a(n) = 0
  have hr7 : r < n := by
    simp at hr1
    apply lt_of_le_of_ne hr1
    by_contra h'
    rw [h', h₁] at hr2
    simp at hr2
  -- now use induction to prove a(r) < a(k) , as we can add up the positive subtractions to a(r)
  have hr8 (k : ℕ) (hk : r < k) (hk': k ≤ n) : a r < a k := by
    induction' k, hk using Nat.le_induction with m hm hm'
    . specialize hr6 r (by omega) (by omega)
      linarith
    . specialize hm' (by linarith)
      specialize hr6 m (by omega) (by omega)
      linarith
  -- now  0 < a (r) < a(n) = 0 contradiction
  specialize hr8 n (by assumption) (by simp)
  rw [h₁] at hr8
  linarith