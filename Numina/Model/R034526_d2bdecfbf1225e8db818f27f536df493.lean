import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_223174 {f : ℝ → ℝ} (hf : f = λ x => x^2 - 2 * x + 3)
  (a : ℝ) (ha : 0 < a) :
  IsGreatest (image f (Icc 0 a)) 3 ∧ IsLeast (image f (Icc 0 a)) 2 ↔
  1 ≤ a ∧ a ≤ 2 := by
  constructor
  · -- Assume that 3 is the greatest and 2 is the least in the image of f over [0,a]
    intro h
    rcases h with ⟨hGreatest, hLeast⟩
    have h1 : 3 ∈ image f (Icc (0 : ℝ) a) := hGreatest.left
    have h2 : ∀ y ∈ image f (Icc (0 : ℝ) a), y ≤ 3 := hGreatest.right
    have h3 : 2 ∈ image f (Icc (0 : ℝ) a) := hLeast.left
    have h4 : ∀ y ∈ image f (Icc (0 : ℝ) a), 2 ≤ y := hLeast.right
    have h5 : a ∈ Icc (0 : ℝ) a := by
      exact ⟨by linarith, by linarith⟩
    have h6 : f a ∈ image f (Icc (0 : ℝ) a) := ⟨a, h5, rfl⟩
    have h7 : f a ≤ 3 := h2 (f a) h6
    have h8 : f a = a ^ 2 - 2 * a + 3 := by
      rw [hf]
    rw [h8] at h7
    have h9 : a ≤ 2 := by
      nlinarith [show a ≥ 0 from by linarith, show a > 0 from ha]
    -- Solving for a in the inequality a^2 - 2*a + 3 ≤ 3
    rcases h3 with ⟨x, hx, hx2⟩
    have hx1 : x ∈ Icc (0 : ℝ) a := hx
    have hfx : f x = 2 := hx2
    have h10 : f x = x ^ 2 - 2 * x + 3 := by
      rw [hf]
    rw [h10] at hfx
    have hx_eq : x = 1 := by
      nlinarith [sq_nonneg (x - 1)]
    rw [hx_eq] at hx1
    have ha1 : 1 ≤ a := by
      have h2 : (0 : ℝ) ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ a := by
        exact hx1
      linarith
    exact ⟨ha1, h9⟩
  · -- Assume 1 ≤ a ≤ 2, prove that 3 is the greatest and 2 is the least in the image
    rintro ⟨ha1, ha2⟩
    constructor
    · -- Prove that 3 is the greatest in the image
      constructor
      · -- Show that 3 is in the image
        use 0
        constructor
        · -- Show that 0 is in the interval
          exact ⟨by linarith, by linarith⟩
        · -- Show that f(0) = 3
          simp [hf]
      · -- Show that 3 is the greatest
        intro y hy
        rcases hy with ⟨x, hx, hx2⟩
        have hx1 : x ∈ Icc (0 : ℝ) a := hx
        have h1 : (0 : ℝ) ≤ x ∧ x ≤ a := by
          exact hx1
        have hfx_eq : f x = x ^ 2 - 2 * x + 3 := by
          rw [hf]
        rw [hfx_eq] at hx2
        have h2 : f x ≤ 3 := by
          nlinarith [show x ≥ 0 from by linarith [h1.left], show x ≤ 2 from by linarith [h1.right, ha2]]
        linarith
    · -- Prove that 2 is the least in the image
      constructor
      · -- Show that 2 is in the image
        use 1
        constructor
        · -- Show that 1 is in the interval
          exact ⟨by linarith, by linarith⟩
        · -- Show that f(1) = 2
          simp [hf]
          <;> nlinarith
      · -- Show that 2 is the least
        intro y hy
        rcases hy with ⟨x, hx, hx2⟩
        have hx1 : x ∈ Icc (0 : ℝ) a := hx
        have h1 : (0 : ℝ) ≤ x ∧ x ≤ a := by
          exact hx1
        have hfx_eq : f x = x ^ 2 - 2 * x + 3 := by
          rw [hf]
        rw [hfx_eq] at hx2
        have h2 : 2 ≤ f x := by
          nlinarith [sq_nonneg (x - 1)]
        linarith