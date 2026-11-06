import Mathlib

theorem algebra_20733 {f : ℝ → ℝ} (h : ∀ x y, f x + f y = f (x + y) - x * y - 1)
    (h1 : f 1 = 1) :
    {n : ℤ | f n = n} = {1, -2} := by 
  have f0 : f 0 = -1 := by
    specialize h 0 0
    norm_num at h 
    linarith

  have eq1 : ∀ (n : ℤ), f n = ((n : ℝ) ^ 2 + 3 * (n : ℝ) - 2) / 2 := by
    intro n
    have eq2 : ∀ (n : ℕ), f ((↑n : ℝ)) = ((↑n : ℝ) ^ 2 + 3 * (↑n : ℝ) - 2) / 2 := by
      intro n
      induction n with
      | zero =>
        simp [f0]
        <;> norm_num
        <;> linarith
      | succ n ih =>
        have eq3 : f ((↑(n + 1 : ℕ) : ℝ)) = f ((↑n : ℝ) + 1) := by
          simp at *
          <;> ring_nf <;> norm_num 
        rw [eq3]
        have eq4 : f ((↑n : ℝ) + 1) = f ((↑n : ℝ)) + (↑n : ℝ) + 2 := by
          have eq5 : f ((↑n : ℝ)) + f 1 = f ((↑n : ℝ) + 1) - (↑n : ℝ) * 1 - 1 := by
            apply h 
          rw [h1] at eq5
          linarith
        rw [eq4]
        rw [ih]
        field_simp
        ring_nf
        <;> norm_num 
        all_goals try { 
          linarith 
        }
    have eq3 : ∀ (n : ℕ), f ((-(↑n : ℝ) : ℝ)) = ((↑n : ℝ) ^ 2 - 3 * (↑n : ℝ) - 2) / 2 := by
      intro n 
      induction n with
      | zero => 
        norm_num [f0]
        all_goals try { 
          linarith 
        }
      | succ n ih =>
        have eq4 : f (-(↑(n + 1 : ℕ) : ℝ)) = f (-(↑n : ℝ) - 1 : ℝ) := by
          simp at *
          <;> ring_nf <;> norm_num 
        rw [eq4]
        have eq5 : f (-(↑n : ℝ) - 1) = f (-(↑n : ℝ)) + (↑n : ℝ) - 1 := by
          have eq6 : f (-(↑n : ℝ)) + f (-1 : ℝ) = f (-(↑n : ℝ) + -1 : ℝ) - (-(↑n : ℝ)) * (-1 : ℝ) - 1 := by 
            apply h 
          have f_1_eq : f (-1 : ℝ) = -2 := by
            have eq7 : f (-1 : ℝ) + f 1 = f ((-1 : ℝ) + 1) - (-1 : ℝ) * 1 - 1 := by 
              apply h 
            rw [h1] at eq7
            norm_num at eq7 ⊢ 
            linarith 
          rw [f_1_eq] at eq6
          have eq8 : f (-(↑n : ℝ) + -1 : ℝ) = f (-(↑n : ℝ) - 1 : ℝ) := by 
            ring_nf 
          rw [eq8] at eq6
          linarith 
        rw [eq5]
        rw [ih]
        field_simp 
        ring_nf 
        <;> norm_num 
        all_goals try { 
          nlinarith 
        }
    cases n with
    | ofNat n => 
      specialize eq2 n 
      norm_num at eq2 ⊢
      try { 
        linarith 
      }
      all_goals try { 
        norm_num at eq2 ⊢ 
        <;> try { 
          linarith 
        } 
      }
    | negSucc n => 
      specialize eq3 (n + 1)
      simp at eq3 ⊢ 
      try { 
        linarith 
      }
      all_goals try { 
        have hn : (↑n : ℝ) + 1 = (↑(n + 1 : ℕ) : ℝ) := by simp 
        rw [hn] at eq3 
        linarith 
      }
  ext n 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor 
  · -- Assume f n = n, prove n = 1 or n = -2
    intro h_eq
    have h7 : f ((↑n : ℝ)) = (↑n : ℝ) := by 
      simpa using h_eq
    have eq1' := eq1 n
    rw [eq1'] at h7 
    have h8 : (n : ℝ) ^ 2 + (n : ℝ) - 2 = 0 := by 
      nlinarith 
    have h10 : n ^ 2 + n - 2 = 0 := by 
      exact_mod_cast h8 
    have h11 : (n + 2) * (n - 1) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h11) with h12 h13
    · -- n + 2 = 0, so n = -2
      have hn2 : n = -2 := by 
        linarith 
      tauto 
    · -- n - 1 = 0, so n = 1
      have hn1 : n = 1 := by 
        linarith 
      tauto 
  · -- Assume n = 1 or n = -2, prove f n = n
    rintro (rfl | rfl)
    · -- n = 1 
      specialize eq1 1 
      norm_num at eq1 ⊢ 
      linarith 
    · -- n = -2 
      specialize eq1 (-2) 
      norm_num at eq1 ⊢ 
      linarith 
  all_goals try { 
    nlinarith 
  }
  all_goals try { 
    linarith 
  }
  all_goals try { 
    tauto 
  }
  all_goals try { 
    nlinarith 
  }
  all_goals try { 
    tauto 
  }
  all_goals try { 
    nlinarith 
    <;> tauto 
  }
  all_goals try { 
    nlinarith 
    <;> tauto 
  }
  all_goals try { 
    nlinarith 
  }
  all_goals try { 
    tauto 
  }
  all_goals try { 
    nlinarith 
  }
  all_goals try { 
    tauto 
  }
  all_goals try { 
    nlinarith 
  }
  all_goals try { 
    tauto 
  }
  all_goals try { 
    nlinarith 
  }
  all_goals try { 
    tauto 
  }