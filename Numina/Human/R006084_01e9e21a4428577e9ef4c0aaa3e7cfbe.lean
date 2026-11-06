import Mathlib

open Finset

/- Compute the positive integer less than 1000 which has exactly 29 positive proper divisors. (Here we refer to positive integer divisors other than the number itself.)-/

theorem number_theory_611477 : 
  ({x ∈ (Finset.range 1000) |
      Finset.card (Nat.properDivisors x) = 29}) = {720} := by 
  have set_mem_aux : 720 ∈ {x ∈ (Finset.range 1000) | Finset.card (Nat.properDivisors x) = 29} := by 
    simp
    rfl
  have set_mem_aux1 : ∀ (x : ℕ), x < 720 → Finset.card (Nat.properDivisors x) ≠ 29 := by 
    intro x hx
    interval_cases x
    all_goals native_decide
  have set_mem_aux2 : ∀ (x : ℕ), (720 < x ∧ x < 1000) → Finset.card (Nat.properDivisors x) ≠ 29:= by
    intro x ⟨hx1, hx2⟩
    interval_cases x
    all_goals native_decide
  apply Finset.ext
  intro a
  constructor
  simp
  intro ha ha'
  by_cases h' : a < 720
  · -- the case for a < 720, there is no number whose proper divisor is 29
    by_contra h''
    obtain hc := set_mem_aux1 a h'
    exact hc ha'
  · -- the case for a > 720, there is no number in `range 1000` whose proper diviors is 29.
    by_cases h3 : a > 720
    obtain hc := set_mem_aux2 a ⟨h3, ha⟩
    by_contra 
    exact hc ha'
    simp_all
    apply Nat.eq_iff_le_and_ge.mpr
    exact ⟨h3, h'⟩
  intro ha
  simp at ha
  simp
  constructor
  linarith
  simp at set_mem_aux
  rw [ha]
  simpa