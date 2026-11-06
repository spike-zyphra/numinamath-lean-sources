import Mathlib

theorem number_theory_144954 (n : ℕ) (h : ∏ i ∈ Finset.range 5, (n + i) = 360360) :
    n + 2 = 13 := by
  have eq1 : ∏ i ∈ Finset.range 5, (n + i) = n * (n + 1) * (n + 2) * (n + 3) * (n + 4) := by
    simp only [Finset.prod_range_succ, add_assoc]
    <;> ring_nf <;> omega
  rw [eq1] at h
  
  -- Now the hypothesis is n * (n + 1) * (n + 2) * (n + 3) * (n + 4) = 360360
  -- Let's prove an upper bound first
  have h1 : n ≤ 13 := by
    by_contra h1
    push_neg at h1
    have h2 : n ≥ 14 := by omega
    have h3 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) ≥ 14 * 15 * 16 * 17 * 18 := by
      have h4 : n ≥ 14 := h2
      have h5 : n + 1 ≥ 15 := by omega
      have h6 : n + 2 ≥ 16 := by omega
      have h7 : n + 3 ≥ 17 := by omega
      have h8 : n + 4 ≥ 18 := by omega
      have h9 : n * (n + 1) * (n + 2) * (n + 3) * (n + 4) ≥ 14 * 15 * 16 * 17 * 18 := by
        apply Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h4 h5) h6) h7) h8
      linarith
    norm_num at h3 h
    linarith
  -- Now find lower bound
  have h2 : n ≥ 11 := by
    -- Proof that n >= 11
    by_contra h2
    push_neg at h2
    have h3 : n ≤ 10 := by omega
    interval_cases n <;> try { simp at h } <;> try { linarith }
  
  -- Now we know n is either 11,12,13
  interval_cases n <;> try { simp at h } <;> try { linarith }