import Mathlib

theorem algebra_255745 :
  { c : ℝ | ∃ v : ℝ, v > 0 ∧ c > 0 ∧ v = 5 ∧
    ∃ t : ℝ, t > 0 ∧ 
    t * c = v * (t + 4.4) ∧
    8 + (t - 8/c - 1/6) * (c + 2) = v * (t + 4.4) } =
  { 16 } := by
  ext c
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume c is in the left side, prove c = 16
    rintro ⟨v, hv, hc_pos, hv_eq, ⟨t, ht_pos, h1, h2⟩⟩
    rw [hv_eq] at h1 h2
    have h3 : t * (c - 5) = 22 := by 
      nlinarith
    have hc1 : c > 5 := by
      nlinarith [h3, ht_pos]
    field_simp at h2 h3
    nlinarith [sq_nonneg (c - 16), sq_nonneg (t - 53 / 15)]
  · -- Assume c = 16, prove c is in the left side
    intro hc
    rw [hc]
    use 5
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    use 2
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num