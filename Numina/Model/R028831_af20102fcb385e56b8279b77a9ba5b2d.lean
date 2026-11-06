import Mathlib

theorem algebra_20919 :
    ∃ (S : Finset ℤ), S = {k | ∃ (a b : ℤ), ∀x, x^2 + k * x + 15 = (x + a) * (x + b)} ∧
    ∏ i ∈ S, i = 16384 := by

  use {-16, -8, 8, 16}
  constructor
  · -- Show that S is the set of all k such that x^2 + k * x + 15 can be factored
    ext k
    simp
    constructor
    · -- Assume k in S
      rintro (rfl | rfl | rfl | rfl)
      · -- k = -16
        exact ⟨-15, -1, fun x => by ring_nf⟩
      · -- k = -8
        exact ⟨-3, -5, fun x => by ring_nf⟩
      · -- k = 8
        exact ⟨3, 5, fun x => by ring_nf⟩
      · -- k = 16
        exact ⟨15, 1, fun x => by ring_nf⟩
    · -- Assume ∃ab such that ∀x, x^2 + k * x + 15 = (x + a) * (x + b)
      rintro ⟨a, b, heq⟩
      have h0 := heq 0
      have h1 := heq 1
      have h2 := heq (-1)
      -- a * b = 15
      have h3 : a * b = 15 := by
        nlinarith
      -- k = a + b
      have h4 : k = a + b := by
        nlinarith
      have h5 : a ∣ 15 := by
        use b
        all_goals linarith
      -- all possible factors
      have h7 : a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 15 ∨ a = -1 ∨ a = -3 ∨ a = -5 ∨ a = -15 := by
        have h7 : a ∣ 15 := by
          use b
          all_goals linarith
        have h8 : a ≤ 15 := by
          apply Int.le_of_dvd (by norm_num) h7
        have h9 : a ≥ -15 := by
          have h9 : -a ∣ 15 := by
            exact Int.neg_dvd.2 h7
          have h10 : -a ≤ 15 := by
            apply Int.le_of_dvd (by norm_num) h9
          linarith
        interval_cases a <;> try { omega }
      rcases h7 with (h7 | h7 | h7 | h7 | h7 | h7 | h7 | h7)
      · -- a = 1, b = 15, k = 16
        rw [h7] at h4
        have h8 : b = 15 := by
          nlinarith
        rw [h8] at h4
        omega
      · -- a = 3, b = 5, k = 8
        rw [h7] at h4
        have h8 : b = 5 := by
          nlinarith
        rw [h8] at h4
        omega
      · -- a = 5, b = 3, k = 8
        rw [h7] at h4
        have h8 : b = 3 := by
          nlinarith
        rw [h8] at h4
        omega
      · -- a = 15, b = 1, k = 16
        rw [h7] at h4
        have h8 : b = 1 := by
          nlinarith
        rw [h8] at h4
        omega
      · -- a = -1, b = -15, k = -16
        rw [h7] at h4
        have h8 : b = -15 := by
          nlinarith
        rw [h8] at h4
        omega
      · -- a = -3, b = -5, k = -8
        rw [h7] at h4
        have h8 : b = -5 := by
          nlinarith
        rw [h8] at h4
        omega
      · -- a = -5, b = -3, k = -8
        rw [h7] at h4
        have h8 : b = -3 := by
          nlinarith
        rw [h8] at h4
        omega
      · -- a = -15, b = -1, k = -16
        rw [h7] at h4
        have h8 : b = -1 := by
          nlinarith
        rw [h8] at h4
        omega
  · -- Show that the product of S is 16384
    native_decide
  all_goals try { tauto }