import Mathlib

theorem inequalities_607167 : {x : ℝ | ⌊x⌋ * Int.fract x < x - 1} = Set.Ici 2 := by 
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_Ici]
  constructor 
  · -- Assume that $\lfloor x \rfloor \cdot \text{frac}(x) < x - 1$, prove that $x \geq 2$ 
    intro h 
    let n := ⌊x⌋
    have hn1 : n ≤ (x : ℝ) := by exact Int.floor_le x 
    have hn2 : (x : ℝ) < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x 
    have hfrac : Int.fract x = (x : ℝ) - (n : ℝ) := by 
      rw [Int.fract]
      <;> simp 
    rw [hfrac] at h 
    by_cases h5 : n > 1 
    · -- n > 1 
      have hn6 : n ≥ 2 := by 
        omega 
      have hn7 : (n : ℝ) ≥ (2 : ℝ) := by 
        exact_mod_cast hn6 
      have hn6 : (n : ℝ) > (1 : ℝ) := by 
        have hn4 : n ≥ 2 := by 
          omega 
        have hn5 : (n : ℝ) ≥ (2 : ℝ) := by 
          exact_mod_cast hn4 
        linarith 
      have hn8 : (n - 1 : ℝ) > 0 := by 
        nlinarith 
      nlinarith 
    by_cases h5 : n < 1 
    · -- n < 1 
      have hn6 : n ≤ 0 := by 
        omega 
      have hn7 : (n : ℝ) ≤ (0 : ℝ) := by 
        exact_mod_cast hn6 
      nlinarith 
    · -- 1 ≤ n ≤ 1 
      have hn6 : n = 1 := by 
        omega 
      have hn7 : (n : ℝ) = (1 : ℝ) := by 
        exact_mod_cast hn6 
      nlinarith 
  · -- Assume that $x \geq 2$, prove that $\lfloor x\rfloor \cdot \text{frac}(x) < x - 1$ 
    intro h 
    let n := ⌊x⌋
    have hn1 : n ≤ (x : ℝ) := by exact Int.floor_le x
    have hn2 : (x : ℝ) < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
    have hn3 : n ≥ 2 := by
      by_contra h
      push_neg at h 
      have : n ≤ 1 := by 
        omega 
      have hn4 : (n : ℝ) ≤ (1 : ℝ) := by 
        exact_mod_cast this 
      nlinarith 
    have hn4 : (n : ℝ) ≥ (2 : ℝ) := by 
      have : n ≥ 2 := by
        omega 
      exact_mod_cast this 
    have hfrac : Int.fract x = (x : ℝ) - (n : ℝ) := by 
      rw [Int.fract]
      <;> simp 
    rw [hfrac] 
    have hn6 : (n - 1 : ℝ) > 0 := by 
      have hn7 : (n : ℝ) ≥ (2 : ℝ) := by 
        have hn6 : n ≥ 2 := by
          omega 
        exact_mod_cast hn6 
      nlinarith 
    nlinarith