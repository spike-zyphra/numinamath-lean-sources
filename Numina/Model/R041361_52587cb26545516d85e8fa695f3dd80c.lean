import Mathlib


theorem number_theory_59027 (n : ℤ):
    5 ∣ ∑ i ∈ Finset.range 5, (n + i + 1)^2 ∧ ¬ (∃ m, m^2 = ∑ i ∈ Finset.range 5, (n + i + 1)^2) ∧ 150 ∣ ∑ i ∈ Finset.range 5, (n + i + 1)^2 * ∑ i ∈ Finset.range 5, (n + i + 6)^2 := by
  constructor
  · -- Show $5$ divides $S_1$.
    have h1 : 5 ∣ ∑ i in Finset.range 5, (n + i + 1) ^ 2 := by
      simp [Finset.sum_range_succ]
      ring_nf
      omega
    exact h1
  constructor
  · -- Show that $S_1$ is not a perfect square.
    intro h
    rcases h with ⟨m, hm⟩
    have eq1 : m^2 = 5 * (n^2 + 6 * n + 11) := by
      simp [Finset.sum_range_succ] at hm ⊢
      nlinarith
    have h3 : m^2 % 5 = 0 := by
      omega
    have h4 : m % 5 = 0 := by
      have h30 : m^2 % 5 = 0 := h3
      have h40 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by
        omega
      rcases h40 with (h | h | h | h | h) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h] at h30 <;> tauto
    have h7 : ∃ t : ℤ, m = 5 * t := by 
      refine' ⟨m / 5, by omega⟩
    rcases h7 with ⟨t, ht⟩
    have eq2 : 5 * t^2 = n^2 + 6 * n + 11 := by
      rw [ht] at eq1
      nlinarith
    have eq3 : (n + 3 : ℤ) ^ 2 % 5 = 3 := by
      have eq6 : (n + 3) ^ 2 = 5 * t^2 - 2 := by
        nlinarith
      omega
    have eq4 : (n + 3 : ℤ) ^ 2 % 5 = 0 ∨ (n + 3 : ℤ) ^ 2 % 5 = 1 ∨ (n + 3 : ℤ) ^ 2 % 5 = 4 := by
      have h1 : (n + 3) % 5 = 0 ∨ (n + 3) % 5 = 1 ∨ (n + 3) % 5 = 2 ∨ (n + 3) % 5 = 3 ∨ (n + 3) % 5 = 4 := by
        omega
      rcases h1 with (h1 | h1 | h1 | h1 | h1) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h1, Int.ofNat] at *
    omega
  · -- Show $150$ divides $S_1 \cdot S_2$.
    have h3 : 150 ∣ ∑ i ∈ Finset.range 5, (n + i + 1)^2 * ∑ i ∈ Finset.range 5, (n + i + 6)^2 := by
      have eq1 : ∑ i in Finset.range 5, (n + i + 1) ^ 2 * ∑ i in Finset.range 5, (n + i + 6) ^ 2 =
          (5 * (n^2 + 6 * n + 11)) * (5 * (n^2 + 16 * n + 66)) := by
        simp [Finset.sum_range_succ]
        all_goals
          ring_nf
      rw [eq1]
      have h4 : ((5 * (n^2 + 6 * n + 11) : ℤ) * (5 * (n^2 + 16 * n + 66) : ℤ)) % 2 = 0 := by
        have h700 : (5 * (n^2 + 6 * n + 11) : ℤ) % 2 = (n^2 + 1) % 2 := by
          omega
        have h701 : (5 * (n^2 + 16 * n + 66) : ℤ) % 2 = (n^2) % 2 := by
          omega
        have h131 : (n) % 2 = 0 ∨ (n) % 2 = 1 := by omega
        rcases h131 with (h131 | h131)
        · simp [Int.mul_emod, h700, h701, pow_two, Int.add_emod, h131]
        · simp [Int.mul_emod, h700, h701, pow_two, Int.add_emod, h131]
      have h5 : ((5 * (n^2 + 6 * n + 11) : ℤ) * (5 * (n^2 + 16 * n + 66) : ℤ)) % 3 = 0 := by
        have h700 : (5 * (n^2 + 6 * n + 11) : ℤ) % 3 = (2 * (n^2) + 1) % 3 := by
          omega
        have h701 : (5 * (n^2 + 16 * n + 66) : ℤ) % 3 = (2 * (n^2) + 2 * (n) ) % 3 := by
          omega
        have h131 : (n) % 3 = 0 ∨ (n) % 3 = 1 ∨ (n) % 3 = 2 := by omega
        rcases h131 with (h131 | h131 | h131)
        · simp [Int.mul_emod, h700, h701, pow_two, Int.add_emod, h131]
        · simp [Int.mul_emod, h700, h701, pow_two, Int.add_emod, h131]
        · simp [Int.mul_emod, h700, h701, pow_two, Int.add_emod, h131]
      have h25 : ((5 * (n^2 + 6 * n + 11) : ℤ) * (5 * (n^2 + 16 * n + 66) : ℤ)) % 25 = 0 := by
        ring_nf
        have h700 : (25 * (n^4) + 1250 * n^3 + 1875 * n^2 + 1250 * n + 3025) % 25 = 0 := by
          ring_nf
          omega
        omega
      omega
    exact h3