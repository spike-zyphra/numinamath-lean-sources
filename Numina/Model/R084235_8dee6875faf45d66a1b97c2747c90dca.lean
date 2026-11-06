import Mathlib

open Set Real

theorem algebra_12819 {a : ℝ} (ha : 2 * a + 1 ≤ 3 * a - 5) :
    (Icc (2 * a + 1) (3 * a - 5)) ⊆ (Icc 3 22) ↔ 6 ≤ a ∧ a ≤ 9 := by
  constructor
  · -- Assume (Icc (2 * a + 1) (3 * a - 5)) ⊆ (Icc 3 22) prove 6 ≤ a ∧ a ≤ 9
    intro h
    -- Because $A$ is non-empty, by hypothesis $2a+1 \leq 3a-5$, we have $a \geq 6$.
    have h1 : 2 * a + 1 ≤ 3 * a - 5 := by linarith
    -- Use $A\subseteq A\cap B$ implies that all element in $A$ is in $B$; get left bound.
    have h2 : 2 * a + 1 ≥ 3 := by 
      have h3 : 2 * a + 1 ∈ (Icc (2 * a + 1) (3 * a - 5)) := by 
        exact mem_Icc.mpr ⟨by linarith, by linarith⟩
      have h4 : 2 * a + 1 ∈ (Icc 3 22) := h h3
      have h5 : 3 ≤ (2 * a + 1 : ℝ) := by 
        simpa using h4.1
      linarith

    -- Use $A\subseteq A\cap B$ implies that all element in $A$ is in $B$; get right bound.
    have h5 : (3 * a - 5 : ℝ) ≤ (22 : ℝ) := by 
      have h6 : (3 * a - 5 : ℝ) ∈ (Icc (2 * a + 1 : ℝ) (3 * a - 5 : ℝ)) := by 
        exact mem_Icc.mpr ⟨by linarith, by linarith⟩
      have h7 : (3 * a - 5 : ℝ) ∈ (Icc 3 22 : Set ℝ) := h h6
      have h8 : (3 * a - 5 : ℝ) ≤ (22 : ℝ) := by 
        simpa using h7.2
      linarith

    -- Thus $a \leq 9$
    have h10 : a ≤ 9 := by 
      linarith

    -- Thus $a \geq 6$, from solving $A$ is not empty.
    have h11 : 6 ≤ a := by
      nlinarith

    constructor
    · exact h11
    · exact h10
  · -- Assume 6 ≤ a ∧ a ≤ 9 prove (Icc (2 * a + 1) (3 * a - 5)) ⊆ (Icc 3 22)
    rintro ⟨h1, h2⟩
    intro x hx
    have h3 : x ≥ (2 * a + 1) := hx.1
    have h4 : x ≤ (3 * a - 5) := hx.2

    -- Show that $x \geq 3$
    have h5 : 3 ≤ x := by
      nlinarith

    -- Show that $x \leq 22$
    have h6 : x ≤ 22 := by
      nlinarith

    exact ⟨h5, h6⟩