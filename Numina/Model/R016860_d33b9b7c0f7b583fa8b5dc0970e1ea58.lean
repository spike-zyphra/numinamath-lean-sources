import Mathlib

theorem number_theory_311190 (M : Finset ℕ) (hM : M = Finset.Icc 1 2017)
    (x : ℕ) (hx : x ∈ M) (hsum : ∃ k, ∑ i ∈ M \ {x}, i = k^2) :
    x = 1677 := by
  rw [hM] at hx hsum
  rcases hsum with ⟨k, hk⟩
  have hx1 : x ≥ 1 := by
    have h1 : x ∈ Finset.Icc 1 2017 := hx
    simp at h1 ⊢
    omega
  have hx2 : x ≤ 2017 := by
    have h1 : x ∈ Finset.Icc 1 2017 := hx
    simp at h1 ⊢
    omega
  have h1 : ∑ i in Finset.Icc 1 2017 \ {x}, i = k ^ 2 := hk
  have h3 : ∑ i in Finset.Icc 1 2017 \ {x}, i = (∑ i in Finset.Icc 1 2017, i) - (∑ i in ({x} : Finset ℕ), i) := by
    have h10 : {x} ⊆ Finset.Icc 1 2017 := by
      intro y hy
      simp at hy ⊢
      rcases hy with ⟨rfl, hy1⟩
      have h1 : x ∈ Finset.Icc 1 2017 := hx
      simp at h1 ⊢
      omega
    rw [← Finset.sum_sdiff h10]
    all_goals
      simp
  have h6 : ∑ i in ({x} : Finset ℕ), i = x := by
    simp
  have h7 : ∑ i in Finset.Icc 1 2017, i = 2035153 := by
    native_decide
  rw [h6, h7] at h3
  rw [h3] at h1
  have hk1 : 2035153 - x = k ^ 2 := by
    omega
  have hk2 : k ^ 2 ≤ 2035153 := by
    have hx1 : x ≥ 1 := by linarith
    omega
  have hk3 : k ≤ 1426 := by
    nlinarith
  have hk4 : k ≥ 1426 := by
    have hk8 : k ^ 2 ≥ 2033136 := by
      have hk9 : x ≤ 2017 := by linarith
      omega
    have hk10 : k ≥ 1426 := by
      nlinarith
    linarith
  have hk5 : k = 1426 := by
    omega
  rw [hk5] at hk1
  have hk7 : x = 1677 := by
    omega
  exact hk7