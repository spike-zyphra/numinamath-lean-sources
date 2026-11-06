import Mathlib

theorem algebra_233219 (a : ℝ) (ha : a ≠ 0) (S : ℕ → ℝ)
    (hS : ∀ i ∈ Finset.range 2018, S (i + 1) = 2 / S i) (hS1 : S 0 = a) :
    S 2017 = 2 / a := by
  have h1 : ∀ n, n < 2018 → (n % 2 = 0 → S n = a) ∧ (n % 2 = 1 → S n = 2 / a) := by
    intro n hn
    induction n with
    | zero =>
      constructor
      · -- Assume 0 % 2 = 0, which is true, so conclude S 0 = a
        simp [hS1]
      · -- Assume 0 % 2 = 1, which is false, so the implication is vacuously true
        simp [hS1]
    | succ n ih =>
      have h2 : n < 2018 := by omega
      rcases ih h2 with ⟨h_even, h_odd⟩
      constructor
      · -- Prove ((n + 1) % 2 = 0 → S (n + 1) = a)
        intro h
        have hn1 : n % 2 = 1 := by omega
        have h2 : S (n + 1) = 2 / S n := hS n (Finset.mem_range.mpr (show n < 2018 by omega))
        have h3 : S n = 2 / a := h_odd hn1
        rw [h2, h3]
        field_simp [ha]
      · -- Prove ((n + 1) % 2 = 1 → S (n + 1) = 2 / a)
        intro h
        have hn1 : n % 2 = 0 := by omega
        have h2 : S (n + 1) = 2 / S n := hS n (Finset.mem_range.mpr (show n < 2018 by omega))
        have h3 : S n = a := h_even hn1
        rw [h2, h3]
        all_goals field_simp [ha]
  have h2017 := (h1 2017 (by norm_num)).2
  norm_num at h2017 ⊢
  <;> linarith