import Mathlib

/- Given a_0 , a_1 , ... , a_n , satisfying a_0 = a_n = 0, and and a_(k-1) - 2a_k + a_(k+1) >= 0 for k=0, 1, ... , n-1. Prove that all the numbers are negative or zero. -/
theorem inequalities_140388 (n : ℕ) (a : ℕ → ℝ)
    (h₀ : a 0 = 0) (h₁ : a n = 0)
    (h₂ : ∀ k ∈ Finset.range n, a (k - 1) - 2 * a k + a (k + 1) ≥ 0) :
    ∀ i ∈ Finset.range (n + 1), a i ≤ 0 := by
  -- if n = 0 or 1 trivially true
  match n with
  | 0 => simp [h₀]
  | 1 =>
    simp
    rintro i hi
    interval_cases i <;> simp [h₀, h₁]
  | m + 1 =>
    -- the condition h₂ means that consecutive differences are non-decreasing
    replace h₂ (k : ℕ) (hk : k ∈ Finset.range (m + 1)) : a k - a (k - 1) ≤ a (k + 1) - a k := by
      specialize h₂ k hk
      linarith
    -- assume there is some element in range that is positive
    by_contra h
    simp at h
    -- choose smallest such elemet
    let s := Nat.find h
    obtain ⟨hs, has⟩ : s < m + 2 ∧  0 < a s := Nat.find_spec h
    -- the element is greater than 0 as a(0) = 0
    have hs' : 0 < s := by
      by_contra hs'
      simp at hs'
      rw [hs', h₀] at has
      simp at has
    -- so a (s-1) ≤ 0
    have : a (s - 1) ≤ 0 := by
      have : s - 1 < s := by omega
      have := Nat.find_min h this
      simp at this
      exact this (by linarith)
    -- for k in [s, m+1] we have a(k) > a(k-1). This is due to the nondecreasing differences and a(s) > a(s-1)
    have h₃ (k : ℕ) (hk : k ∈ Finset.range (m + 2)) (hk' : s ≤ k) : a (k - 1) < a k := by
      induction' k, hk' using Nat.le_induction with l hl hl'
      . linarith
      . simp at hk hl'
        specialize hl' (by linarith)
        simp
        specialize h₂ l (by simpa)
        linarith
    -- by last fact for k in [s, m+1], a k is positive
    have h₄ (k : ℕ) (hk : k ∈ Finset.range (m + 2)) (hk' : s ≤ k) : 0 < a k := by
      induction' k, hk' using Nat.le_induction with l hl hl'
      . assumption
      . simp at hl' hk
        specialize hl' (by linarith)
        specialize h₃ (l + 1) (by simpa) (by linarith)
        simp at h₃
        linarith
    -- but then a (m+1) is positive, contradiction
    specialize h₄ (m + 1) (by simp) (by linarith)
    rw [h₁] at h₄
    simp at h₄