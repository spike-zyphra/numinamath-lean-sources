import Mathlib

theorem algebra_163852_a :
    {(a, b) : ℤ × ℤ | 0 < a ∧ 0 < b ∧ a * b = 2 * (2 * a + 2 * b)} =
    {(20, 5), (12, 6), (8, 8), (6, 12), (5, 20)} := by 
  ext ⟨a, b⟩
  simp 
  constructor 
  · -- Proof of left side implies right side 
    rintro ⟨ha, hb, heq⟩
    have h1 : a * b = 4 * (a + b) := by 
      nlinarith 
    have h2 : a ≤ 20 := by 
      by_contra h
      push_neg at h
      have h3 : b ≤ 4 := by 
        nlinarith [show 0 < b by linarith, show 0 < a by linarith, sq_nonneg (a - 20 : ℤ), sq_nonneg (b - 5 : ℤ)]
      interval_cases b <;> omega 
    have h3 : b ≤ 20 := by 
      by_contra h 
      push_neg at h 
      have h4 : a ≤ 4 := by 
        nlinarith [show 0 < a by linarith, show 0 < b by linarith, sq_nonneg (a - 5 : ℤ), sq_nonneg (b - 20 : ℤ)]
      interval_cases a <;> omega 
    interval_cases a <;> omega 
  · -- Proof of right side to left side 
    intro h 
    rcases h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals 
      constructor <;> norm_num <;> omega

theorem algebra_163852_b :
    {(e, f) : ℤ × ℤ | 0 < e ∧ 0 < f ∧ e * e * f = 2 * (2 * e * e + 4 * e * f)} =
    {(40, 5), (24, 6), (16, 8), (12, 12), (10, 20), (9, 36)} := by 
  ext ⟨e, f⟩ 
  simp 
  constructor 
  · -- Proof of (e,f) in left side implies (e,f) in right side 
    rintro ⟨he1, hf1, hef⟩
    have h1 : e * e * f = 4 * e * e + 8 * e * f := by 
      nlinarith 
    have h2 : e * f = 4 * e + 8 * f := by 
      nlinarith 
    have h3 : (e - 8) * (f - 4) = 32 := by 
      nlinarith 
    have h4 : e ≤ 40 := by
      have h5 : (e - 8) * (f - 4) = 32 := h3 
      have h6 : e - 8 ∣ 32 := by 
        use f - 4 
        all_goals linarith 
      have h7 : e - 8 ≤ 32 := by 
        apply Int.le_of_dvd (show 0 < 32 by norm_num) h6 
      omega 
    have h5 : f ≤ 36 := by
      have h6 : (e - 8) * (f - 4) = 32 := h3 
      have h7 : f - 4 ∣ 32 := by 
        use e - 8 
        all_goals linarith 
      have h8 : f - 4 ≤ 32 := by 
        apply Int.le_of_dvd (show 0 < 32 by norm_num) h7 
      omega 
    interval_cases e <;> omega 
  · -- Proof of (e,f) in right side implies (e,f) in left side 
    rintro (h | h | h | h | h | h)
    · -- (e, f) = (40, 5)
      rcases h with ⟨rfl, rfl⟩ 
      constructor 
      · norm_num 
      constructor 
      · norm_num
      · norm_num 
    · -- (e, f) = (24, 6)
      rcases h with ⟨rfl, rfl⟩ 
      constructor 
      · norm_num 
      constructor 
      · norm_num
      · norm_num 
    · -- (e, f) = (16, 8)
      rcases h with ⟨rfl, rfl⟩ 
      constructor 
      · norm_num 
      constructor 
      · norm_num
      · norm_num 
    · -- (e, f) = (12, 12)
      rcases h with ⟨rfl, rfl⟩ 
      constructor 
      · norm_num 
      constructor 
      · norm_num
      · norm_num 
    · -- (e, f) = (10, 20)
      rcases h with ⟨rfl, rfl⟩ 
      constructor 
      · norm_num 
      constructor 
      · norm_num
      · norm_num 
    · -- (e, f) = (9, 36)
      rcases h with ⟨rfl, rfl⟩ 
      constructor 
      · norm_num 
      constructor 
      · norm_num
      · norm_num