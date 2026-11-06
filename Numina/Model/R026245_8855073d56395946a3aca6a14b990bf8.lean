import Mathlib

theorem number_theory_237418 :
    ∃ m n, (2015^2 + 2017^2) / 2 = m^2 + n^2 ∧
    ∀ a b, Odd a → Odd b → a ≠ b → ∃ c d, (a^2 + b^2) / 2 = c^2 + d^2 := by

  use 2016, 1
  constructor
  · -- Show that (2015^2 + 2017^2) / 2 = 2016^2 + 1^2
    norm_num
  · -- Prove the more general fact
    intro a b ha hb hneq
    have h1 : a % 2 = 1 := by
      rcases ha with ⟨m, hm⟩
      omega
    have h2 : b % 2 = 1 := by
      rcases hb with ⟨n, hn⟩
      omega
    have h3 : (a - b) % 2 = 0 := by
      omega
    have h4 : ∃ k : ℕ, a = b + 2 * k ∨ b = a + 2 * k := by
      by_cases h : a ≥ b
      · -- If a ≥ b, then a - b is even
        have : (a - b) % 2 = 0 := h3
        have h5 : ∃ k : ℕ, a - b = 2 * k := by
          refine' ⟨(a - b) / 2, by omega⟩
        rcases h5 with ⟨k, hk⟩
        have ha_eq : a = b + 2 * k := by
          omega
        exact ⟨k, Or.inl ha_eq⟩
      · -- If b > a, then b - a is even
        have : (b - a) % 2 = 0 := by
          omega
        have h5 : ∃ k : ℕ, b - a = 2 * k := by
          refine' ⟨(b - a) / 2, by omega⟩
        rcases h5 with ⟨k, hk⟩
        have hb_eq : b = a + 2 * k := by
          omega
        exact ⟨k, Or.inr hb_eq⟩
    rcases h4 with ⟨k, hk⟩
    rcases hk with (hak | hbk)
    · -- Case where a = b + 2k
      have h5 : (a ^ 2 + b ^ 2) / 2 = (b + k) ^ 2 + k ^ 2 := by
        rw [hak]
        ring_nf
        <;> omega
      exact ⟨b + k, k, by linarith [h5]⟩
    · -- Case where b = a + 2k
      have h5 : (a ^ 2 + b ^ 2) / 2 = (a + k) ^ 2 + k ^ 2 := by
        rw [hbk]
        ring_nf
        <;> omega
      exact ⟨a + k, k, by linarith [h5]⟩