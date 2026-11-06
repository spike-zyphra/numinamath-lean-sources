import Mathlib

theorem algebra_100336 {a b c d : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (h : ∀ n, ∃ k, Odd k ∧ k > n ∧ ∀ i ∈ Finset.range k, (a * ⌊Real.sqrt (b * i + c)⌋ + d) = k) :
    a + b + c + d = 3 := by
  by_contra h1
  have h1' := h 0
  rcases h1' with ⟨k0, hk0_odd, hk0_gt, hk0⟩
  have hk0_odd' : k0 % 2 = 1 := by
    obtain ⟨m, hm⟩ := hk0_odd
    omega
  have h2 := h (k0 + 1)
  rcases h2 with ⟨k1, hk1_odd, hk1_gt, hk1⟩
  have hk1_odd' : k1 % 2 = 1 := by
    obtain ⟨m, hm⟩ := hk1_odd
    omega
  have h3 := h (k1 + 1)
  rcases h3 with ⟨k2, hk2_odd, hk2_gt, hk2⟩
  have hk2_odd' : k2 % 2 = 1 := by
    obtain ⟨m, hm⟩ := hk2_odd
    omega
  have eq1 := hk1 0 (by
    have : k1 > 0 := by
      omega
    simp [this]
  )
  have eq2 := hk2 0 (by
    have : k2 > 0 := by
      omega
    simp [this]
  )
  have h4 : (k1 : ℝ) = (k2 : ℝ) := by
    linarith [eq1, eq2]
  have h5 : k1 = k2 := by
    exact_mod_cast h4
  have h6 : k2 > k1 := by
    omega
  have h7 : k1 < k1 := by
    nlinarith [h5, h6]
  linarith