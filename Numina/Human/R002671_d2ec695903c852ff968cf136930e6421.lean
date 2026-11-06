import Mathlib

/- Let m be a positive integer, and let a_0, a_1, …, a_m​ be a sequence of reals such that
a_0 = 37, a_1 = 72, a_m = 0, and a_{k+1} = a_{k−1} − 3 / a_k​ for k = 1, 2, …, m − 1. Find m. -/
theorem algebra_98605 (m : ℕ) (hm : m > 0) (a : ℕ → ℝ)
    (ha0 : a 0 = 37) (ha1 : a 1 = 72) (ham : a m = 0)
    (hak : ∀ k ∈ Finset.Icc 1 (m - 1), a k ≠ 0 ∧ a (k + 1) = a (k - 1) - 3 / a k) : m = 889 := by
  -- define p(k) = a(k) * a(k + 1)
  set p : ℕ → ℝ := fun k => a k * a (k + 1)
  -- for all k ∈ [1, m - 1], p(k) = p(k - 1) - 3 (it follows directly from the assumption hak)
  have hp : ∀ k ∈ Finset.Icc 1 (m - 1), p k = p (k - 1) - 3 := by
    intro k hk
    have ⟨ha0, heq⟩ := hak k hk
    simp [p, heq]
    field_simp
    left
    congr
    simp at hk
    omega
  -- we need to show that 2 ≤ m which follows from a(m) = 0 and a(1) ≠ 0
  have hm2 : 2 ≤ m := by
    contrapose! ham
    replace h : m = 1 := by omega
    simp [h, ha1]
  -- show that for all k ∈ [1, m - 1], p(k) = 2664 - 3 * k
  have hp_ind : ∀ k ∈ Finset.Icc 1 (m - 1), p k = 2664 - 3 * k := by
    intro k
    -- proof by induction
    induction k with
    | zero => simp
    | succ k ih =>
      -- consider two cases k = 1 and k = k' + 2
      cases k with
      | zero =>
        -- if k = 1 then p(1) = a(1) * a(2) = 72 * (37 - 3 / 72) = 2664 - 3
        simp [p, ha1]
        intro _
        have ⟨_, h2⟩ := hak 1 (by simp; omega)
        rw [h2, ha0, ha1]
        norm_num
      | succ k =>
        -- if k = k' + 2 then the result follows from the induction hypothesis:
        -- p(k' + 2) = p(k' + 1) - 3 (from hp) = 2664 - 3 * (k' + 1) - 3 = 2664 - 3 * (k' + 2)
        simp at ih ⊢
        intro hk2
        rw [hp (k + 2) (by simp; omega), add_assoc]; norm_num
        rw [ih (by omega)]
        ring
  -- we have p(m - 1) = a(m - 1) * a(m) = a(m - 1) * 0 = 0
  have hp0 : p (m - 1) = 0 := by simp [p, show m - 1 + 1 = m by omega]; right; exact ham
  specialize hp_ind (m - 1) (show m - 1 ∈ Finset.Icc 1 (m - 1) by simp; omega)
  -- we derive the equation 0 = p(m - 1) = 2664 - 3 * (m - 1)
  -- its solution is m = 889
  rw [hp0] at hp_ind
  push_cast [show 1 ≤ m by omega] at hp_ind
  rify
  linarith