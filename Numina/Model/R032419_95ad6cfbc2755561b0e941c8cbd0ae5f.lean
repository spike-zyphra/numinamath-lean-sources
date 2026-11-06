import Mathlib

theorem algebra_93625 {m n : ℝ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hangle : Real.arctan m = 2 * Real.arctan n) (hmp : m = 4 * n) :
    m * n = 2 := by
  have h1 : Real.tan (Real.arctan m) = m := by 
    rw [Real.tan_arctan]
  have h2 : Real.tan (Real.arctan n) = n := by 
    rw [Real.tan_arctan]
  have h3 : Real.tan (Real.arctan m) = Real.tan (2 * Real.arctan n) := by 
    rw [hangle]
  have htan2 : Real.tan (2 * Real.arctan n) = (2 * n) / (1 - n ^ 2) := by
    rw [Real.tan_two_mul, h2]
    <;> ring_nf <;> field_simp [(show (1 - n ^ 2) ≠ 0 by
      by_contra h'
      have hne : n ^ 2 = 1 := by linarith
      have hne2 : n = 1 ∨ n = -1 := by
        have : n ^ 2 = 1 := by linarith
        rw [sq_eq_one_iff] at this
        tauto
      cases hne2 with
      | inl h11 =>
        rw [h11] at hangle h1 h2 h3
        norm_num [h11] at hangle h1 h2 h3
        all_goals try { contradiction }
      | inr h22 =>
        rw [h22] at hangle h1 h2 h3
        norm_num [h22] at hangle h1 h2 h3
        all_goals try { contradiction }
    )]
    all_goals
    ring_nf <;> nlinarith
  
  rw [htan2] at h3
  rw [h1] at h3
  rw [hmp] at h3
  have h5 : (4 * n) * (1 - n ^ 2) = 2 * n := by
    by_cases hne : 1 - n ^ 2 = 0
    · -- First case: 1 - n^2 = 0, so n^2 = 1
      exfalso
      have hn2_eq_one : n ^ 2 = 1 := by
        nlinarith 
      have hn_eq_one_or_neg_one : n = 1 ∨ n = -1 := by
        have : n ^ 2 = 1 := hn2_eq_one
        rw [sq_eq_one_iff] at this
        tauto
      cases hn_eq_one_or_neg_one with
      | inl hn_eq_one =>
        rw [hn_eq_one] at h3 hn
        norm_num at h3 hn
        all_goals try { exfalso } <;> try { tauto } <;> try { nlinarith }
        all_goals try { contradiction }
        all_goals try { tauto }
        all_goals try { linarith [hn] }
      | inr hn_eq_neg_one =>
        rw [hn_eq_neg_one] at h3 hn
        norm_num at h3 hn
        all_goals try { exfalso } <;> try { tauto } <;> try { nlinarith }
        all_goals try { contradiction }
        all_goals try { tauto }
        all_goals try { linarith [hn] }
    · -- Second case: 1 - n^2 ≠ 0, so can cross-multiply
      field_simp [hne] at h3 ⊢
      nlinarith 
  have h6 : 2 * n * (1 - 2 * n ^ 2) = 0 := by
    nlinarith 
  have hn2 : n ^ 2 = 1 / 2 := by
    cases (mul_eq_zero.1 h6) with
    | inl h11 =>
      exfalso
      apply hn
      linarith
    | inr h11 =>
      nlinarith 
  have h7 : m * n = 4 * n ^ 2 := by
    rw [hmp]
    all_goals 
    ring
  rw [h7]
  rw [hn2]
  all_goals
    norm_num
    all_goals
    try { tauto }
    all_goals
    try { 
      nlinarith 
    }
    <;> try { 
      exfalso <;> all_goals try { tauto }
    }
  all_goals
  try { linarith [hn] }
  all_goals
  try { tauto }
  all_goals
  try { 
    nlinarith 
  }
  <;> try { 
    exfalso <;> all_goals try { tauto }
  }
  all_goals
  try { tauto }
  all_goals
  try { 
    nlinarith 
  }
  <;> try { 
    exfalso <;> all_goals try { tauto }
  }
  all_goals
  try { tauto }
  all_goals
  try { 
    nlinarith 
  }
  <;> try { 
    exfalso <;> all_goals try { tauto }
  }