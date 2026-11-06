import Mathlib

open Real Set
open scoped BigOperators

/-
  Suppose $p$: the real number $x$ satisfies $(x-3a)(x-a) < 0$, where $a > 0$, and $q$:
  the real number $x$ satisfies $\begin{cases} x^{2}-3x\leqslant 0\\x^{2}-x-2 > 0\end{cases}$,
  if $p$ is a necessary but not sufficient condition for $\lnot q$,
  find the range of values for the real number $a$.
-/
theorem algebra_9039 {a : ℝ} (ha : 0 < a) (hp : p = fun x : ℝ => (x - 3 * a) * (x - a) < 0)
    (hq : q = fun x : ℝ => x ^ 2 - 3 * x ≤ 0 ∧ x ^ 2 - x - 2 > 0) :
    (¬ (∀ x, p x → ¬ q x)) ∧ (∀ x, ¬ q x → p x) ↔ false := by

  -- solve the equation hq : x ∈ (2, 3]
  have solve_q {x : ℝ} : q x ↔ x ∈ Set.Ioc 2 3 := by
    constructor
    · -- by factoring
      intro hx
      simp [hq] at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      have hle : x * (x - 3) ≤ 0 := by
        calc
          x * (x - 3) = x ^ 2 - 3 * x := by ring
          _ ≤ 0 := by exact tsub_nonpos.mpr h1
      apply mul_nonpos_iff.mp at hle
      have hgt : (x + 1) * (x - 2) > 0 := by
        calc
          (x + 1) * (x - 2) = x ^ 2 - x - 2 := by ring
          _ > 0 := by exact sub_pos.mpr h2
      apply mul_pos_iff.mp at hgt
      rcases hle with hl | hr
      · obtain ⟨h3, h4⟩ := hl
        have : x ≤ 3 := by exact tsub_nonpos.mp h4
        simp [this]
        rcases hgt with hl' | hr'
        · obtain hl' := hl'.right
          exact lt_add_neg_iff_lt.mp hl'
        · obtain ⟨h5, h6⟩ := hr'
          linarith
      · obtain ⟨h3, h4⟩ := hr
        linarith
    · -- verify the answer
      intro hx
      simp [hq] at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      constructor
      · have hle : x * (x - 3) ≤ 0 := by
          apply mul_nonpos_iff.mpr
          apply Or.inl
          constructor <;> linarith
        linarith
      · have hgt : (x + 1) * (x - 2) > 0 := by
          apply mul_pos_iff.mpr
          apply Or.inl
          constructor <;> linarith
        linarith

  -- solve the equations at hp : x ∈ (x, 3 * a)
  have solve_p {x : ℝ} : p x ↔ x ∈ Set.Ioo a (3 * a) := by
    simp [hp]
    constructor
    · -- by factoring
      intro hx
      apply mul_neg_iff.mp at hx
      rcases hx with h | h
      · obtain ⟨h1, h2⟩ := h
        have : 3 * a < a := by linarith
        have : a < 0 := by linarith [this]
        linarith
      · constructor <;> linarith
    · -- verify
      intro hx
      apply mul_neg_iff.mpr
      apply Or.inr
      constructor <;> linarith

  -- prove no such a exists
  simp
  intro x hpx hqx
  apply solve_p.mp at hpx
  apply solve_q.mp at hqx
  use 0
  constructor
  · apply (Iff.not solve_q).mpr
    simp
  · apply (Iff.not solve_p).mpr
    simp [ha]
    exact le_of_lt ha
