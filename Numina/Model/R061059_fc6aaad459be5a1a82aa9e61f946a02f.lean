import Mathlib

theorem number_theory_267364 :
    Set.ncard {n : ℕ | 0 < n ∧ 7 ∣ n ∧ √n ∈ Set.Ioo 17 18} = 5 := by
  have h1 : {n : ℕ | 0 < n ∧ 7 ∣ n ∧ √n ∈ Set.Ioo 17 18} = {294, 301, 308, 315, 322} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume n belongs to the set
      intro h
      rcases h with ⟨hn_pos, hn_div, hsqrt⟩
      rcases hsqrt with ⟨h1, h2⟩
      have h289 : 289 < (n : ℝ) := by
        have h17 : (17 : ℝ) < √n := by
          linarith [h1]
        have h4 : (17 : ℝ) ^ 2 < (n : ℝ) := by
          rw [Real.lt_sqrt] at h17
          all_goals nlinarith
        nlinarith
      have h324 : (n : ℝ) < (324 : ℝ) := by
        have h18 : √n < (18 : ℝ) := by
          linarith [h2]
        have h5 : (n : ℝ) < (18 : ℝ) ^ 2 := by
          rw [Real.sqrt_lt] at h18
          all_goals nlinarith
        nlinarith
      have h3 : n > 289 := by
        have h : (n : ℝ) > (289 : ℝ) := by linarith
        exact_mod_cast h
      have h4 : n < 324 := by
        have h : (n : ℝ) < (324 : ℝ) := by linarith
        exact_mod_cast h
      interval_cases n <;> norm_num at *
      <;> tauto
    · -- Show that if n ∈ {294, 301, 308, 315, 322}, then it satisfies the conditions
      rintro (rfl | rfl | rfl | rfl | rfl)
      · -- n = 294
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show sqrt(294) ∈ (17, 18)
          have h1 : 17 < Real.sqrt 294 := by
            rw [Real.lt_sqrt] <;> norm_num
          have h2 : Real.sqrt 294 < 18 := by
            rw [Real.sqrt_lt] <;> norm_num
          exact ⟨h1, h2⟩
      · -- n = 301
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show sqrt(301) ∈ (17, 18)
          have h1 : 17 < Real.sqrt 301 := by
            rw [Real.lt_sqrt] <;> norm_num
          have h2 : Real.sqrt 301 < 18 := by
            rw [Real.sqrt_lt] <;> norm_num
          exact ⟨h1, h2⟩
      · -- n = 308
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show sqrt(308) ∈ (17, 18)
          have h1 : 17 < Real.sqrt 308 := by
            rw [Real.lt_sqrt] <;> norm_num
          have h2 : Real.sqrt 308 < 18 := by
            rw [Real.sqrt_lt] <;> norm_num
          exact ⟨h1, h2⟩
      · -- n = 315
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show sqrt(315) ∈ (17, 18)
          have h1 : 17 < Real.sqrt 315 := by
            rw [Real.lt_sqrt] <;> norm_num
          have h2 : Real.sqrt 315 < 18 := by
            rw [Real.sqrt_lt] <;> norm_num
          exact ⟨h1, h2⟩
      · -- n = 322
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Show sqrt(322) ∈ (17, 18)
          have h1 : 17 < Real.sqrt 322 := by
            rw [Real.lt_sqrt] <;> norm_num
          have h2 : Real.sqrt 322 < 18 := by
            rw [Real.sqrt_lt] <;> norm_num
          exact ⟨h1, h2⟩
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }