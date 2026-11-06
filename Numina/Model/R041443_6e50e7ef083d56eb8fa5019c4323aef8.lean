import Mathlib

theorem number_theory_220047 (x : ℝ) :
    ⌊x⌋ * (x - ⌊x⌋) = 2009 * x ↔ x = 0 ∨ x = -1 / 2010 := by
  constructor
  · -- Assume $\lfloor x\rfloor \cdot (x - \lfloor x\rfloor) = 2009 \cdot x$, prove $x = 0 \vee x = -1/2010$
    intro h
    let n := ⌊x⌋
    have hn1 : n ≤ (x : ℝ) := by exact Int.floor_le x
    have hn2 : (x : ℝ) < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
    have h_eq : (n : ℝ) * (x - (n : ℝ)) = 2009 * x := by
      simpa using h
    have hn3 : (n : ℝ) ≤ (x : ℝ) := by exact_mod_cast hn1
    have hn4 : (x : ℝ) < (n + 1 : ℝ) := by exact_mod_cast hn2
    have h7 : n ≤ 0 := by
      by_contra h8
      push_neg at h8
      have hn8 : n ≥ 1 := by omega
      have h8' : (n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast hn8
      nlinarith
    have h8 : n ≥ -1 := by
      by_contra h9
      push_neg at h9
      have hn9 : n ≤ -2 := by omega
      have h9' : (n : ℝ) ≤ (-2 : ℝ) := by exact_mod_cast hn9
      nlinarith
    have hn8 : n = 0 ∨ n = -1 := by omega
    rcases hn8 with (h9 | h9)
    · -- n = 0
      have hn9' : (n : ℝ) = (0 : ℝ) := by
        exact_mod_cast h9
      have hx : x = (0 : ℝ) := by
        rw [hn9'] at h_eq
        nlinarith
      left
      exact_mod_cast hx
    · -- n = -1
      have hn9' : (n : ℝ) = (-1 : ℝ) := by
        exact_mod_cast h9
      have hx : x = (-1 / 2010 : ℝ) := by
        rw [hn9'] at h_eq
        nlinarith
      right
      exact_mod_cast hx
  · -- Assume x = 0 ∨ x = -1/2010, prove $\lfloor x\rfloor \cdot (x - \lfloor x\rfloor) = 2009 \cdot x$
    rintro (h | h)
    · -- x = 0
      rw [h]
      norm_num
    · -- x = -1/2010
      rw [h]
      norm_num [Int.floor_eq_iff]