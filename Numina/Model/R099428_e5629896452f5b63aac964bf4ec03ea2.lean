import Mathlib

theorem number_theory_65097 :
    IsLeast {x | ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ q = p + 2 ∧ x = (p + q) / 2} 4 := by
  constructor
  · use 3, 5
    all_goals norm_num
  · rintro x ⟨p, q, hp, hq, h1, h2⟩
    have h3 : p ≥ 3 := by
      by_contra h
      push_neg at h
      have hp2 : p < 3 := h
      have hp2' : p ≤ 2 := by linarith
      interval_cases p <;> norm_num [h1] at hp hq
      <;> try { try { contradiction } <;> try { norm_num } <;> try { omega } }
      <;> norm_num
      all_goals norm_num
      <;> try { omega }
 
    have h4 : q ≥ 5 := by linarith [h1, h3]

    have h5 : x ≥ 4 := by
      rw [h2]
      -- Since p >=3 and q >=5
      have hp3 : p ≥ 3 := h3
      have hq5 : q ≥ 5 := by linarith [h1, h3]
      -- Then p + q >=8
      have h6 : p + q ≥ 8 := by omega
      -- Therefore (p + q) / 2 >=4
      omega

    linarith