import Mathlib

theorem number_theory_15915 : IsGreatest {b : ℕ | ∃ a c : ℕ, 1 < c ∧ c < b ∧ b < a ∧ a * b * c = 240} 10 := by
  constructor
  · -- Show 10 is in the set
    use 12, 2
    all_goals norm_num
  · -- Show no larger element is in the set
    intro b hb
    rcases hb with ⟨a, c, hc1, hc2, h1, heq⟩
    by_contra h
    push_neg at h
    have h2 : b ≥ 11 := by omega
    have h3 : a > b := h1
    have h4 : c < b := hc2
    have h5 : c ≥ 2 := by
      omega
    have h6 : a ≥ b + 1 := by
      omega
    have h7 : b ≥ 11 := h2
    have h9 : (a * b * c) ≥ (b * (2 * (b + 1))) := by
      calc
        a * b * c = (a * c) * b := by ring
        _ ≥ (2 * (b + 1)) * b := by
          have h12 : a * c ≥ 2 * (b + 1) := by
            nlinarith
          nlinarith
        _ = (b * (2 * (b + 1))) := by
          ring
    have h35 : (a * b * c) ≥ b * (2 * (b + 1)) := h9
    have h40 : b * (2 * (b + 1)) ≥ 11 * 24 := by
      have h55 : b ≥ 11 := h7
      nlinarith
    nlinarith [h35, heq, h40]