import Mathlib

/- Let $[x]$ be the integer part of a number $x$, and $\{x\}=x-[x]$. Solve the equation
$$ [x] \cdot\{x\}=1991 x $$ -/
theorem number_theory_605712 (x : ℝ) :⌊x⌋ * (x - ⌊x⌋) = 1991 * x ↔ x = -1 / 1992 ∨ x = 0 := by
    constructor
  -- the forward direction --
    . by_cases hx: x = 0
      -- case x = 0 --
      . simp [hx]
      -- case x ≠ 0 --
      . intro h
        left  -- show x = -1 / 1992 --
        by_cases b: x > 0
        -- for the case x > 0 --
        . clear hx
          have ineq1: ⌊x⌋ ≤ x := by
            apply Int.floor_le
          have ineq2: x - ⌊x⌋ < 1 := by
            have h1:= Int.lt_floor_add_one x
            nlinarith
          -- ineq1,2 gives the following bound --
          have bound: ⌊x⌋ * (x - ⌊x⌋) < x := by
            nlinarith
          rw [h] at bound
          absurd bound
          simp
          nlinarith
        -- for the case x < 0 --
        . simp at b
          have hb: x < 0 := by
            by_contra! no
            have l: x = 0 := by linarith
            tauto
          clear hx b
          by_cases h1: -1 < x
          -- for the case -1 < x --
          . have eq: ⌊x⌋ = -1 := by
              rw [Int.floor_eq_iff]
              constructor
              . simp
                linarith
              . simp
                linarith
            rw [eq] at h
            simp at h
            nlinarith
          -- for the case x ≤ -1 --
          . clear hb
            simp at h1
            have neg: (⌊x⌋: ℝ) < 0 := by
              have s: ⌊x⌋ ≤ x := by
                apply Int.floor_le
              calc
                ⌊x⌋  ≤ x := by exact s
                  _ ≤  -1 := by exact h1
                  _ < 0 := by norm_num
            have ineq1: ⌊x⌋ > x - 1 := by
              simp
            have ineq2: x - ⌊x⌋ < 1 := by
              linarith
            have bound: ⌊x⌋ * (x - ⌊x⌋) > (x - 1) := by nlinarith
            rw [h] at bound
            have contra: x > -1/1990 := by nlinarith
            nlinarith

  -- the backward direction --
    . intro h
      rcases h with h | h
      . rw [h]
        norm_num
      . rw [h]
        norm_num