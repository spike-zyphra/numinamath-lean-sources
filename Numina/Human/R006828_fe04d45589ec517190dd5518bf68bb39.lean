import Mathlib

/-Let a and k be positive integers. Let M be the integer ak+1.
Find the unique integer x such that ax≡1(modM) and 0 ≤ x< M.
Show that x= M−k.-/

theorem number_theory_641542 (a k x M: ℤ) (ha: 0 < a) (hk: 0 < k) (hM: M = a * k + 1)
  (hx: 0 ≤ x ∧ x < M ∧ a * x % M = 1) (h: ∃! x, 0 ≤ x ∧ x < M ∧ a * x % M = 1): x = M - k := by

  set y:= M - k

  -- it suffices to show that y is a solution
  have hy: 0 ≤ y ∧ y < M ∧ a * y % M = 1 := by
    constructor
    .
      simp [y, hM]
      nlinarith
    .
      constructor
      .
        simp [y, hM]
        nlinarith
      .
        simp [y]
        rw [show a * (M - k) = M * (a - 1) + 1 by simp [hM]; ring]
        rw [Int.add_emod]
        suffices M * (a - 1) % M = 0 by
          simp [this]
          apply Int.emod_eq_of_lt
          omega
          rw [hM]
          nlinarith
        simp

  obtain ⟨p, hp, h⟩ := h
  have fx:= h x hx
  have fy:= h y hy
  omega

