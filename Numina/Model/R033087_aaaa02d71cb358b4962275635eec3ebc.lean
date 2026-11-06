import Mathlib

theorem number_theory_11844 (a b : ℤ) (ha : a ≡ 18 [ZMOD 42]) (hb : b ≡ 73 [ZMOD 42]) :
    {n | n ∈ Finset.Icc 100 141 ∧ (a - b ≡ n [ZMOD 42])} = {113} := by
  have h1 : a - b ≡ 29 [ZMOD 42] := by
    norm_num [Int.ModEq] at ha hb ⊢
    omega
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume n ∈ {n | n ∈ Finset.Icc 100 141 ∧ (a - b ≡ n [ZMOD 42])}
    rintro ⟨⟨hn1, hn2⟩, hn3⟩
    have h2 : (a - b) % 42 = (29 : ℤ) := by
      have h1' : a - b ≡ 29 [ZMOD 42] := h1
      simp [Int.ModEq] at h1' ⊢
      omega
    have h4 : (a - b) % 42 = (n) % 42 := by
      simp [Int.ModEq] at hn3 ⊢
      omega
    have h3 : (29 : ℤ) % 42 = (n : ℤ) % 42 := by
      omega
    omega
  · -- Show that n=113 satisfies the conditions
    intro hn
    rw [hn]
    constructor
    · -- Show 113 is in [100, 141]
      norm_num
    · -- Show a - b ≡ 113 [ZMOD 42]
      have h2 : a - b ≡ (29 : ℤ) [ZMOD 42] := h1
      have h113 : (29 : ℤ) ≡ (113 : ℤ) [ZMOD 42] := by
        norm_num [Int.ModEq]
      have h3 : a - b ≡ (113 : ℤ) [ZMOD 42] := by
        exact Int.ModEq.trans h2 h113
      exact h3