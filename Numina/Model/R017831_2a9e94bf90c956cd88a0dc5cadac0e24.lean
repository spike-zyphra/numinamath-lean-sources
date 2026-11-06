import Mathlib

theorem calculus_22287 (ω : ℂ) (hω : ω^3 = 1) :
    {v | v = 1 / (1 + ω) + 1 / (1 + ω^2)} = {1} := by

  have h1 : 1 / (1 + ω) + 1 / (1 + ω ^ 2) = 1 := by

    by_cases h_eq1 : ω = 1

    · 
      rw [h_eq1]
      norm_num

    · 
      have h3 : ω^2 + ω + 1 = 0 := by
        have eq : ω^3 - 1 = 0 := by
          rw [hω]
          ring
        have eq2 : ω^3 - 1 = (ω - 1) * (ω^2 + ω + 1) := by ring
        rw [eq2] at eq
        cases' (mul_eq_zero.mp eq) with h4 h5
        · 
          have hω1 : ω = 1 := by
            have h : ω - 1 = 0 := h4
            calc
              ω = (ω - 1) + 1 := by ring
              _ = 0 + 1 := by rw [h]
              _ = 1 := by ring
          tauto
        · 
          exact h5

      have h4 : (1 + ω) ≠ 0 := by
        by_contra h
        have h_eq0 : ω = -1 := by
          have h_eq0 : 1 + ω = 0 := h
          calc
            ω = (1 + ω) - 1 := by ring
            _ = 0 - 1 := by rw [h_eq0]
            _ = -1 := by ring
        have h_eq0 : ω^3 = -1 := by
          rw [h_eq0]
          norm_num
        rw [h_eq0] at hω
        norm_num at hω

      have h5 : (1 + ω^2) ≠ 0 := by
        by_contra h
        have h_eq0 : ω^2 = -1 := by
          have h_eq0 : 1 + ω^2 = 0 := h
          calc
            ω^2 = (1 + ω^2) - 1 := by ring
            _ = 0 - 1 := by rw [h_eq0]
            _ = -1 := by ring
        have h_eq0 : ω^3 = -ω := by
          calc
            ω^3 = ω * ω^2 := by ring
            _ = ω * (-1) := by rw [h_eq0]
            _ = -ω := by ring
        have h_eq0' : ω = -1 := by
          have eq1 : ω^3 = 1 := by
            exact hω
          have eq2 : ω^3 = -ω := h_eq0
          have eq3 : -ω = 1 := by
            rw [eq2] at eq1
            exact eq1
          have eq4 : ω = -1 := by
            calc
              ω = -ω * (-1) := by ring
              _ = 1 * (-1) := by rw [eq3]
              _ = -1 := by ring
          exact eq4
        have h_eq0'' : ω^3 = -1 := by
          rw [h_eq0']
          norm_num
        rw [h_eq0''] at hω
        norm_num at hω

      calc
        1 / (1 + ω) + 1 / (1 + ω^2) = (1 + ω^2) / ((1 + ω) * (1 + ω^2)) + (1 + ω) / ((1 + ω^2) * (1 + ω)) := by 
          field_simp [h4, h5]
          <;> ring
        _ = (1 + ω^2 + 1 + ω) / ((1 + ω) * (1 + ω^2)) := by 
          ring_nf
        _ = (2 + ω + ω^2) / ((1 + ω) * (1 + ω^2)) := by 
          ring
        _ = (2 + (ω + ω^2)) / ((1 + ω) * (1 + ω^2)) := by 
          ring
        _ = (2 + (-1)) / ((1 + ω) * (1 + ω^2)) := by 
          have h_eq0 : ω + ω^2 = -1 := by
            have h_eq0 : ω^2 + ω + 1 = 0 := h3
            have h_eq1 : ω + ω^2 = -1 := by
              calc
                ω + ω^2 = (ω^2 + ω + 1) - 1 := by ring
                _ = -1 := by rw [h_eq0]; ring
            exact h_eq1
          rw [h_eq0]
        _ = 1 / ((1 + ω) * (1 + ω^2)) := by 
          rw [show (2 + (-1) : ℂ) = 1 by norm_num]
        _ = 1 / (1 : ℂ) := by 
          have h_eq0 : (1 + ω) * (1 + ω^2) = 1 := by
            calc
              (1 + ω) * (1 + ω^2) = 1 + ω + ω^2 + ω^3 := by ring
              _ = 1 + ω + ω^2 + 1 := by rw [hω]
              _ = 2 + ω + ω^2 := by ring
              _ = 1 := by
                have h_eq0 : ω + ω^2 = -1 := by
                  have h_eq0 : ω^2 + ω + 1 = 0 := h3
                  have h_eq1 : ω + ω^2 = -1 := by
                    calc
                      ω + ω^2 = (ω^2 + ω + 1) - 1 := by ring
                      _ = -1 := by rw [h_eq0]; ring
                  exact h_eq1
                calc
                  2 + ω + ω^2 = 2 + (ω + ω^2) := by ring
                  _ = 2 + (-1) := by rw [h_eq0]
                  _ = 1 := by norm_num
          rw [h_eq0]
        _ = 1 := by 
          norm_num

  ext v
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- If v = 1 / (1 + ω) + 1 / (1 + ω^2), then v = 1.
    intro h
    rw [h]
    exact h1
  · -- If v = 1, then v = 1 / (1 + ω) + 1 / (1 + ω^2).
    intro h
    rw [h]
    exact Eq.symm h1