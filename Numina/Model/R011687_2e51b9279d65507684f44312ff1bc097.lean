import Mathlib

theorem number_theory_272215 (d e : ℤ) (hd : Odd d) (he : Even e) (a: ℕ → ℤ)
 (h1: a 1 = d + d) (h2: a 2 = (e + e) * d) (h3: a 3 = d * d) (h4: a 4 = d * (e + d)):
    {i: ℕ | 1 ≤ i ∧ i ≤ 4 ∧ Odd (a i)}.encard = 2 := by

  have h1' : ¬ Odd (a 1) := by 
    rw [h1]
    have : d % 2 = 1 := by 
      obtain ⟨k, hk⟩ := hd 
      omega
    intro h 
    obtain ⟨k, hk⟩ := h 
    have eq1 : d + d = 2 * k + 1 := by 
      linarith [hk] 
    have eq2 : (d + d : ℤ) % 2 = 0 := by 
      have : d % 2 = 1 := by 
        omega
      omega 
    have eq3 : (2 * k + 1 : ℤ) % 2 = 1 := by 
      omega 
    omega

  have h2' : ¬ Odd (a 2) := by 
    rw [h2]
    have h1 : d % 2 = 1 := by 
      obtain ⟨k, hk⟩ := hd 
      omega 
    have h2 : e % 2 = 0 := by 
      obtain ⟨k, hk⟩ := he 
      omega 
    intro h 
    obtain ⟨k, hk⟩ := h 
    have eq1 : (e + e) * d = 2 * k + 1 := by 
      linarith [hk] 
    have eq : (e + e) * d = 2 * e * d := by 
      ring 
    rw [eq] at eq1 
    have h4 : (2 * e * d : ℤ) % 2 = 0 := by 
      have : e % 2 = 0 := h2 
      simp [Int.mul_emod, Int.add_emod, Int.sub_emod] 
    have eq3 : (2 * k + 1 : ℤ) % 2 = 1 := by 
      omega 
    omega

  have h3' : Odd (a 3) := by 
    rw [h3]
    obtain ⟨k, hk⟩ := hd 
    rw [show d = 2 * k + 1 by linarith] 
    use 2 * k ^ 2 + 2 * k 
    all_goals 
    ring_nf 
  have h4' : Odd (a 4) := by 
    rw [h4]
    have h5 : Odd d := hd 
    have he' : Even e := he 
    obtain ⟨k, hk⟩ := h5 
    obtain ⟨s, hs⟩ := he' 
    have h7 : Odd (e + d) := by 
      use k + s 
      linarith 
    have h8 : Odd (d * (e + d)) := by 
      apply Odd.mul 
      all_goals 
      try { exact hd } 
      all_goals 
      try { exact h7 } 
    exact h8 
  have h5 : {i: ℕ | 1 ≤ i ∧ i ≤ 4 ∧ Odd (a i)} = {3, 4} := by 
    ext i 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor 
    · -- Forward implication 
      rintro ⟨hi1, hi2, h6⟩ 
      interval_cases i <;> norm_num [h1', h2', h3', h4'] at h6 ⊢ 
      all_goals tauto 
    · -- Backward implication 
      rintro (rfl | rfl)
      · -- i = 3
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        exact h3' 
      · -- i = 4
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        exact h4' 
  rw [h5] 
  rw [Set.encard] 
  simp [Set.ncard_pair]