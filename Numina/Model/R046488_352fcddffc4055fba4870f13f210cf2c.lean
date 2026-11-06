import Mathlib

/- Nine consecutive positive integers are arranged in ascending order to form a sequence ${{a}_{1}},{{a}_{2}},\cdots ,{{a}_{8}}$. If the value of ${{a}_{1}}+{{a}_{3}}+{{a}_{5}}+{{a}_{7}}+{{a}_{9}}$ is a perfect square, and the value of ${{a}_{2}}+{{a}_{4}}+{{a}_{6}}+{{a}_{8}}$ is a perfect cube, then the minimum value of the sum of these nine positive integers is ___          ___. -/
theorem number_theory_11609 (a : ℕ) (ha : a > 0) (h1 : ∃ k, a + a + 2 + a + 4 + a + 6 + a + 8 = k^2)
    (h2 : ∃ m, a + 1 + a + 3 + a + 5 + a + 7 = m^3) :
    a + (a + 1) + (a + 2) + (a + 3) + (a + 4) + (a + 5) + (a + 6) + (a + 7) + (a + 8) ≥ 18000 := by
  rcases h1 with ⟨k, hk⟩
  rcases h2 with ⟨m, hm⟩
  have h3 : 5 * a + 20 = k ^ 2 := by
    nlinarith 
  have h4 : 4 * a + 16 = m ^ 3 := by 
    nlinarith 
  have h5 : m > 0 := by 
    by_contra h
    push_neg at h 
    have h6 : m ≤ 0 := by linarith 
    have h7 : m ^ 3 ≤ 0 := by 
      have h1 : m ≤ 0 := h6 
      have h2 : m ^ 3 ≤ (0 : ℕ) ^ 3 := by 
        apply Nat.pow_le_pow_of_le_left 
        all_goals linarith 
      norm_num at h2 ⊢ 
      linarith 
    nlinarith [h4, show a > 0 by linarith]
  -- Relation between k and m
  have eq1 : 5 * m ^ 3 = 4 * k ^ 2 := by
    have eq_a1 : a = (m ^ 3 - 16) / 4 := by 
      omega 
    rw [eq_a1] at h3 
    have : 5 * m ^ 3 = 4 * k ^ 2 := by 
      omega 
    assumption 
  have h13 : m ≥ 20 := by 
    by_contra h 
    push_neg at h 
    have h6 : m < 20 := by linarith 
    have h8 : k ≥ 5 := by 
      nlinarith [h3, ha]
    interval_cases m <;> try { 
      have : k < 100 := by
        nlinarith [h3, ha]
      interval_cases k <;> omega 
    }
    <;> omega 
  -- $m \geq 20$ implies $a \geq 1996$
  have eq3 : a ≥ 1996 := by
    have h9 : m ≥ 20 := h13 
    have h10 : m ^ 3 ≥ 8000 := by
      have h11 : m ≥ 20 := h9 
      have h12 : m ^ 3 ≥ (20 : ℕ) ^ 3 := by 
        apply Nat.pow_le_pow_of_le_left 
        all_goals linarith 
      norm_num at h12 ⊢ 
      linarith 
    -- $4 * a + 16 = m^3$
    have h13 : 4 * a + 16 ≥ 8000 := by 
      linarith [h4, h10]
    omega
  -- Final calculation
  have eq4 : a + (a + 1) + (a + 2) + (a + 3) + (a + 4) + (a + 5) + (a + 6) + (a + 7) + (a + 8) = 9 * a + 36 := by 
    ring 
  nlinarith [eq4, eq3]
  all_goals linarith
  <;> try { tauto }