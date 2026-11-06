import Mathlib

open Set Real

theorem inequalities_320046 {P Q : Set ℝ}
    (hP : P = {x | abs (x - 1) < 1}) (hQ : Q = {x | abs (x - a) ≤ 1})
    (hPQ : P ∩ Q = ∅) :
    a ≤ -1 ∨ a ≥ 3 := by
  by_contra h
  push_neg at h 
  have h1 : -1 < a := by linarith [h.1]
  have h2 : a < 3 := by linarith [h.2]
  have h3 : P ∩ Q ≠ ∅ := by
    have h4 : (a + 1) / 2 ∈ P ∩ Q := by
      constructor
      · -- Show that (a + 1) / 2 ∈ P
        rw [hP]
        dsimp
        have h5 : abs (( (a + 1) / 2 ) - 1) < 1 := by
          have h6 : -1 < a := h1
          have h7 : a < 3 := h2
          have h8 : -1 < ( (a + 1) / 2 ) - 1 := by
            linarith
          have h9 : ( (a + 1) / 2 ) - 1 < 1 := by
            linarith
          rw [abs_lt]
          constructor <;> linarith
        simpa using h5
      · -- Show that (a + 1) / 2 ∈ Q
        rw [hQ]
        dsimp
        have h8 : abs (( (a + 1) / 2 ) - a) ≤ 1 := by
          have h9 : -1 < a := h1
          have h10 : a < 3 := h2
          have h14 : -1 ≤ ( (a + 1) / 2 ) - a := by
            linarith
          have h15 : ( (a + 1) / 2 ) - a ≤ 1 := by
            linarith
          apply abs_le.mpr
          constructor <;> linarith
        simpa using h8
    have h5 : (a + 1) / 2 ∈ P ∩ Q := h4
    intro h
    have h6 : (a + 1) / 2 ∈ P ∩ Q := h5
    simp [h] at h6
    all_goals try { contradiction }
    all_goals try { tauto }
    all_goals try { tauto }
  have h4 : (P ∩ Q) = ∅ := hPQ
  have h5 : (P ∩ Q) ≠ ∅ := h3
  contradiction
  all_goals try { tauto }
  all_goals try { tauto }
  all_goals try { tauto }
  all_goals try { tauto }
  all_goals try { tauto }
  all_goals try { tauto }
  all_goals try { tauto }
  all_goals try { tauto }
  all_goals try { tauto }
  all_goals try { tauto }
  all_goals try { tauto }
  all_goals try { tauto }