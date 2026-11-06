import Mathlib

set_option maxHeartbeats 400000


theorem number_theory_608570: (∃ a0 a1 a2 a3 a4 a5 a6: ℝ,
  (a6 = a5 + 1 ∨ a6 = a5 / 2 ∨ a6 = a5 / 3) ∧
  (a5 = a4 + 1 ∨ a5 = a4 / 2 ∨ a5 = a4 / 3) ∧
  (a4 = a3 + 1 ∨ a4 = a3 / 2 ∨ a4 = a3 / 3) ∧
  (a3 = a2 + 1 ∨ a3 = a2 / 2 ∨ a3 = a2 / 3) ∧
  (a2 = a1 + 1 ∨ a2 = a1 / 2 ∨ a2 = a1 / 3) ∧
  (a1 = a0 + 1 ∨ a1 = a0 / 2 ∨ a1 = a0 / 3) ∧
  (a0 = 19 ∧ a6 = 1)) ∧
  (¬ ∃ a0 a1 a2 a3 a4 a5: ℝ,
  (a5 = a4 + 1 ∨ a5 = a4 / 2 ∨ a5 = a4 / 3) ∧
  (a4 = a3 + 1 ∨ a4 = a3 / 2 ∨ a4 = a3 / 3) ∧
  (a3 = a2 + 1 ∨ a3 = a2 / 2 ∨ a3 = a2 / 3) ∧
  (a2 = a1 + 1 ∨ a2 = a1 / 2 ∨ a2 = a1 / 3) ∧
  (a1 = a0 + 1 ∨ a1 = a0 / 2 ∨ a1 = a0 / 3) ∧
  (a0 = 19 ∧ a5 = 1)) ∧
  (¬ ∃ a0 a1 a2 a3 a4: ℝ,
  (a4 = a3 + 1 ∨ a4 = a3 / 2 ∨ a4 = a3 / 3) ∧
  (a3 = a2 + 1 ∨ a3 = a2 / 2 ∨ a3 = a2 / 3) ∧
  (a2 = a1 + 1 ∨ a2 = a1 / 2 ∨ a2 = a1 / 3) ∧
  (a1 = a0 + 1 ∨ a1 = a0 / 2 ∨ a1 = a0 / 3) ∧
  (a0 = 19 ∧ a4 = 1)) := by
    constructor
    .
      use 19
      use 20
      use 10
      use 5
      use 6
      use 2
      use 1
      norm_num
    .
      constructor
      .
        by_contra! h
        obtain ⟨a0, a1, a2, a3, a4, a5, h⟩ := h
        rcases h with ⟨h5,h4,h3,h2,h1,s0,s5⟩
        simp [s5] at h5
        simp [s0] at *
        clear s0 s5
        rcases h1 with h1 | h1 | h1
        <;> rcases h2 with h2 | h2 | h2
        <;> rcases h3 with h3 | h3 | h3
        <;> rcases h4 with h4 | h4 | h4
        <;> rcases h5 with h5 | h5 | h5
        <;> norm_num [h1,h2,h3,h4,h5] at *
        <;> linarith
      .
        by_contra! h
        obtain ⟨a0, a1, a2, a3, a4, h⟩ := h
        rcases h with ⟨h4,h3,h2,h1,s0,s4⟩
        simp [s4] at h4
        simp [s0] at *
        clear s0 s4
        rcases h1 with h1 | h1 | h1
        <;> rcases h2 with h2 | h2 | h2
        <;> rcases h3 with h3 | h3 | h3
        <;> rcases h4 with h4 | h4 | h4
        <;> norm_num [h1,h2,h3,h4] at *
        <;> linarith