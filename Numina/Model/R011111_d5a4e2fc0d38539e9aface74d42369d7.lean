import Mathlib

theorem number_theory_13037 (m n : ℕ)
    (hm : IsLeast {x : ℕ | 0 < x ∧ x.divisors.card = 2} m)
    (hn : IsGreatest {x : ℕ | 0 < x ∧ x < 100 ∧ x.divisors.card = 3} n) :
    m + n = 51 := by
  have hm2 : m = 2 := by
    rcases hm with ⟨hm1, hm2⟩
    have h1 : m ∈ {x : ℕ | 0 < x ∧ x.divisors.card = 2} := hm1
    rcases h1 with ⟨hm_pos, hm_div⟩
    have h2 : m ≥ 2 := by
      by_contra h
      push_neg at h
      have h3 : m < 2 := h
      have h3 : m = 0 ∨ m = 1 := by
        omega
      rcases h3 with (h3 | h3)
      · -- m = 0
        omega
      · -- m = 1
        rw [h3] at hm_div
        all_goals
          try { contradiction }
          all_goals
            native_decide
    have eq1 : m ≤ 2 := by 
      have h3 : m ∈ lowerBounds ( {x : ℕ | 0 < x ∧ x.divisors.card = 2 } ) := hm2
      have h4 : (2 : ℕ) ∈ ( {x : ℕ | 0 < x ∧ x.divisors.card = 2 } ) := by 
        constructor
        · norm_num
        · -- Show that 2 has exactly 2 divisors
          native_decide
      have h5 : m ≤ (2 : ℕ) := by 
        apply h3 
        exact h4 
      linarith 
    have eq : m = 2 := by linarith 
    exact_mod_cast eq
  -- Show that n = 49
  have hn49 : n = 49 := by
    rcases hn with ⟨hn1, hn2⟩
    have h1 : n ∈ {x : ℕ | 0 < x ∧ x < 100 ∧ x.divisors.card = 3} := hn1
    rcases h1 with ⟨hn_pos, hn_lt, hn_div⟩
    have hn49_in : 49 ∈ {x : ℕ | 0 < x ∧ x < 100 ∧ x.divisors.card = 3} := by
      constructor 
      · norm_num
      constructor 
      · norm_num
      · native_decide
    have h5 : 49 ≤ n := by
      apply hn2
      exact hn49_in
    have h6 : n ≤ 49 := by
      by_contra h
      push_neg at h
      have hn50 : n > 49 := h
      interval_cases n <;> norm_num at hn_div <;> contradiction
    linarith
  -- Show m + n = 51
  omega