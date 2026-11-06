import Mathlib

theorem number_theory_631204 : IsLeast {n : ℕ | ∃ a b : ℕ, a ≤ 100 ∧ b ≤ 100 ∧ n = a + b ∧ Real.sqrt 15 < (a / b : ℝ) ∧ (a / b : ℝ) < 4} 39 := by
  set s := Finset.filter (λ(a, b) ↦ 15 * b^2 < a^2 ∧ a < 4 * b) (Finset.Icc 0 100 ×ˢ Finset.Icc 0 100) with hs
  have : {n : ℕ | ∃ a b : ℕ, a ≤ 100 ∧ b ≤ 100 ∧ n = a + b ∧ Real.sqrt 15 < (a / b : ℝ) ∧ (a / b : ℝ) < 4} = {n : ℕ | ∃x ∈ s, n = x.fst + x.snd} := by
    ext n; simp only [exists_and_left, Set.mem_setOf_eq, Prod.exists]
    constructor
    · rintro ⟨a, ha, b, hb, rfl, h1, h2⟩
      use a
      simp only [add_right_inj, exists_eq_right', hs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, zero_le, true_and]
      have hb₁ : 0 < b := by
        by_contra! hb₁
        simp only [nonpos_iff_eq_zero] at hb₁
        rw [hb₁] at h1 h2
        simp only [CharP.cast_eq_zero, div_zero] at h1 h2
        rw [Real.sqrt_lt (by positivity) (by positivity)] at h1
        norm_num at h1
      split_ands
      · omega
      · omega
      · rw [lt_div_iff₀ (by norm_cast), ←Real.sqrt_sq (Nat.cast_nonneg' b), ←Real.sqrt_mul (by linarith), Real.sqrt_lt (by positivity) (by positivity)] at h1
        norm_cast at h1
      · rw [div_lt_iff₀ (by norm_cast)] at h2
        norm_cast at h2
    · rintro ⟨a, b, ha⟩
      simp only [hs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, zero_le, true_and, and_assoc] at ha
      obtain ⟨ha, hb, h1, h2, rfl⟩ := ha
      use a
      use (by omega)
      use b
      simp only [hb, true_and]
      split_ands
      · rw [Real.sqrt_lt (by positivity) (by positivity), div_pow, lt_div_iff₀]
        all_goals norm_cast
        by_contra! h
        simp only [nonpos_iff_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at h
        rw [h] at h1 h2
        norm_num at h1 h2
      · rw [div_lt_iff₀]
        all_goals norm_cast
        by_contra! h
        simp only [nonpos_iff_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at h
        rw [h] at h1 h2
        norm_num at h1 h2
  rw [this]
  have : {n | ∃ x ∈ s, n = x.1 + x.2} = Finset.filter (λn ↦ ∃ x ∈ s, n = x.1 + x.2) (Finset.Icc 0 200) := by
    ext n; simp only [hs, exists_and_left, Set.mem_setOf_eq, Prod.exists, Finset.coe_filter, Finset.mem_Icc, zero_le, true_and, Finset.mem_filter, Finset.mem_product, iff_and_self, forall_exists_index, and_imp]
    omega
  rw [this]
  have : Finset.filter (λn ↦ ∃ x ∈ s, n = x.1 + x.2) (Finset.Icc 0 200) = {64, 69, 74, 78, 79, 83, 84, 119, 88, 89, 93, 94, 98, 99, 39, 103, 104, 123, 44, 108, 109, 49, 113, 114, 117, 54, 118, 122, 59, 124} := by native_decide
  rw [this]
  constructor
  · simp
  · simp
