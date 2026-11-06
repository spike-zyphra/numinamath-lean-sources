import Mathlib

theorem number_theory_709
  (P : ℕ → Prop)
  (hP : ∀ n4, P n4 ↔
    ∃ (a c : ℕ) (f : ℕ → ℕ), (c > 0) ∧ (∀ i, f i = a + c * i) ∧ Nat.Prime (f 0) ∧ Nat.Prime (f 1) ∧ Nat.Prime (f 2) ∧ Nat.Prime (f 3) ∧ Nat.Prime (f 4) ∧ f 4 = n4) :
  IsLeast { x : ℕ | P x } 29 := by
  constructor
  · -- First, show that 29 is in the set
    have h1 : P 29 := by 
      rw [hP]
      use 5, 6, fun i => 5 + 6 * i
      constructor
      · norm_num
      constructor
      · intro i
        simp 
      repeat { constructor }
      all_goals norm_num
    exact h1
  · -- Now, show that 29 is the smallest
    intro n hn
    have h2 : P n := by 
      simpa using hn
    rw [hP] at h2
    rcases h2 with ⟨a, c, f, hc, hf, h0, h1, h2, h3, h4, hn⟩
    by_contra h
    push_neg at h
    have eq0 : f 0 = a := by 
      specialize hf 0 
      norm_num at hf 
      linarith 
    have eq1 : f 1 = a + c := by 
      specialize hf 1 
      norm_num at hf 
      linarith 
    have eq2 : f 2 = a + 2 * c := by 
      specialize hf 2 
      norm_num at hf 
      linarith 
    have eq3 : f 3 = a + 3 * c := by 
      specialize hf 3 
      norm_num at hf 
      linarith 
    have eq4 : f 4 = a + 4 * c := by 
      specialize hf 4 
      norm_num at hf 
      linarith 
    rw [eq0] at h0 
    rw [eq1] at h1 
    rw [eq2] at h2 
    rw [eq3] at h3 
    rw [eq4] at h4 
    have hn_eq : a + 4 * c = n := by 
      linarith [hn, eq4] 
    have h : n < 29 := by linarith 
    have h6 : a ≤ 28 := by 
      omega 
    have hc_le : c ≤ 28 := by 
      omega 
    interval_cases a <;> interval_cases c 
      <;> norm_num [hn_eq] at h0 h1 h2 h3 h4 hn_eq 
      <;> omega