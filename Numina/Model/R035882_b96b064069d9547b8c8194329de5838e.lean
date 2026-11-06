import Mathlib

theorem algebra_10153 {a : ℕ → ℝ} (ha : ∀ i ∈ Finset.range 7, a i = -1 ∨ a i = 1)
    (f : ℝ → ℝ) (hf : f = fun x => a 6 * x ^ 6 + a 5 * x ^ 5 + a 4 * x ^ 4 + a 3 * x ^ 3 + a 2 * x ^ 2 + a 1 * x + a 0)
    (h2 : f 2 = -53) : f 1 = -1 := by
  have h2' : a 6 * (2:ℝ) ^ 6 + a 5 * (2:ℝ) ^ 5 + a 4 * (2:ℝ) ^ 4 + a 3 * (2:ℝ) ^ 3 + a 2 * (2:ℝ) ^ 2 + a 1 * (2:ℝ) + a 0 = -53 := by
    rw [hf] at h2
    simpa using h2

  have ha0 : a 0 = -1 ∨ a 0 = 1 := by
    apply ha 0
    simp [Finset.mem_range]

  have ha1 : a 1 = -1 ∨ a 1 = 1 := by
    apply ha 1
    simp [Finset.mem_range]

  have ha2 : a 2 = -1 ∨ a 2 = 1 := by
    apply ha 2
    simp [Finset.mem_range]

  have ha3 : a 3 = -1 ∨ a 3 = 1 := by
    apply ha 3
    simp [Finset.mem_range]

  have ha4 : a 4 = -1 ∨ a 4 = 1 := by
    apply ha 4
    simp [Finset.mem_range]

  have ha5 : a 5 = -1 ∨ a 5 = 1 := by
    apply ha 5
    simp [Finset.mem_range]

  have ha6 : a 6 = -1 ∨ a 6 = 1 := by
    apply ha 6
    simp [Finset.mem_range]
  rcases ha0 with ha0 | ha0 <;> rcases ha1 with ha1 | ha1 <;> rcases ha2 with ha2 | ha2 <;> rcases ha3 with ha3 | ha3 <;> rcases ha4 with ha4 | ha4 <;> rcases ha5 with ha5 | ha5 <;> rcases ha6 with ha6 | ha6
    <;> norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6] at h2' ⊢
    <;> norm_num [hf, ha0, ha1, ha2, ha3, ha4, ha5, ha6]
    <;> all_goals norm_num <;> tauto