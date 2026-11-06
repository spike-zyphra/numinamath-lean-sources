import Mathlib

theorem number_theory_177631 :
  let s := {(k, n, m) : ℕ × ℕ × ℕ | 0 < k ∧ 0 < n ∧ 0 < m ∧ k * n ^ 2 * (2 * m + 1) = 3808};
  s.ncard = 9 ∧ IsLeast {a | ∃ x ∈ s, a = x.1 * x.2.1 * x.2.2} 408 := by 
  intro s
  have h1 : s = {(544, 1, 3), (136, 2, 3), (34, 4, 3), (224, 1, 8), (56, 2, 8), (14, 4, 8), (32, 1, 59), (8, 2, 59), (2, 4, 59)} := by
    ext ⟨k, n, m⟩
    simp [s]
    constructor
    ·
      rintro ⟨hk, hn, hm, heq⟩
      have h_eq : k * n ^ 2 * (2 * m + 1) = 3808 := heq
      have h3 : m ≤ 59 := by 
        by_contra h
        push_neg at h
        have h2 : 2 * m + 1 > 119 := by linarith 
        have h3 : k * n ^ 2 < 32 := by 
          nlinarith 
        have h4 : k * n ^ 2 ≥ 1 := by 
          have hk1 : k > 0 := by linarith 
          have hn1 : n > 0 := by linarith 
          have : k * n ^ 2 > 0 := by positivity 
          linarith 
        have h5 : n ≤ 5 := by
          by_contra h6 
          push_neg at h6 
          have h7 : n > 5 := by linarith 
          have h8 : k * n ^ 2 ≥ 36 * k := by 
            have h9 : n ^ 2 ≥ 36 := by 
              nlinarith 
            nlinarith 
          nlinarith 
        interval_cases n <;> try { 
          omega 
        }
        all_goals
        have h5 : k ≤ 31 := by
          nlinarith 
        interval_cases k <;> omega 
      have h_eq1 : m = 3 ∨ m = 8 ∨ m = 59 := by 
        have h4 : 2 * m + 1 ∣ 3808 := by 
          use k * n ^ 2 
          nlinarith 
        have h5 : m ≤ 59 := h3 
        interval_cases m <;> norm_num at h4 ⊢ 
      rcases h_eq1 with (rfl | rfl | rfl)
      · -- m=3
        have eq1 : k * n ^ 2 = 544 := by 
          norm_num at h_eq ⊢ 
          nlinarith [h_eq]
        have eq_n : n ≤ 32 := by
          have : n ^ 2 ≤ 544 := by
            nlinarith
          nlinarith 
        interval_cases n <;> try { 
          omega 
        }
      · -- m=8
        have eq1 : k * n ^ 2 = 224 := by
          norm_num at h_eq ⊢ 
          nlinarith [h_eq]
        have eq_n : n ≤ 32 := by
          have : n ^ 2 ≤ 224 := by
            nlinarith 
          nlinarith 
        interval_cases n <;> try { 
          omega 
        }
      · -- m=59
        have eq1 : k * n ^ 2 = 32 := by
          norm_num at h_eq ⊢ 
          nlinarith [h_eq]
        have eq_n : n ≤ 8 := by
          have : n ^ 2 ≤ 32 := by
            nlinarith
          nlinarith 
        interval_cases n <;> try { 
          omega 
        }
    · 
      rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  constructor 
  · -- Show the ncard is 9.
    rw [Set.ncard_eq_toFinset_card']
    simp 
  · -- Show the second part.
    constructor 
    · -- Show existence.
      use (34, 4, 3)
      simp [h1]
    · -- Show minimality.
      intro a h
      rcases h with ⟨x, hx, h_eq⟩
      simp [h1] at hx 
      rcases hx with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
      simp [h_eq] at h_eq ⊢ 
      all_goals
      omega