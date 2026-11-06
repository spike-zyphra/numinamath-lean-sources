import Mathlib

open Real

/-
1. For which values of $a$ does the equation

$$
1+\sin ^{2} a x=\cos x
$$

have a unique solution?
-/
theorem algebra_217121 (a : ℝ):
(∃! x : ℝ, 1 + (sin (a*x))^2 = cos x)
↔
Irrational a := by
  --We simplify the given assumption to the following form.
  have l1 (a x: ℝ) :
  (1 + (sin (a*x))^2 = cos x)
  ↔
  ((∃ (n : ℤ), ↑n * Real.pi = a*x) ∧ (∃ (n : ℤ), ↑n * (2 * Real.pi) = x)) := by 

    constructor <;> intro h

    have t1: 0 ≤ (sin (a*x))^2 := by exact sq_nonneg (sin (a * x))
    have t2: cos x ≤ 1 := by exact cos_le_one x
    have t3: cos x = 1 := by linarith
    have t4: sin (a*x) = 0 := by 
      have : sin (a*x)^2 = 0 := by linarith
      exact pow_eq_zero this
    rw [sin_eq_zero_iff] at t4  
    rw [cos_eq_one_iff] at t3
    tauto

    obtain ⟨h1,h2⟩ := h
    rw [←sin_eq_zero_iff] at h1
    rw [←cos_eq_one_iff] at h2
    simp [h1,h2]
    --Since x=0 is always a solution, the assumption that there is a unique solution is equivalent to that there is not any non-zero solution.
  have l2 (a : ℝ):
    (∃! x:ℝ, 1 + (sin (a*x))^2 = cos x) ↔
    (∀ y ≠ 0, ¬ ((∃ (n : ℤ), ↑n * Real.pi = a*y) ∧ (∃ (n : ℤ), ↑n * (2 * Real.pi) = y))) := by 
    constructor <;> intro h

    intro y yne0 
    by_contra eq
    rw [←l1] at eq
    have : 1 + sin (a*0) ^2 = cos 0 := by simp
    have : y = 0 := by apply ExistsUnique.unique; exact h; exact eq; exact this
    contradiction

    refine existsUnique_of_exists_of_unique ?_ ?_
    use 0
    simp
    intro y1 y2 hy1 hy2
    rw [l1] at hy1 hy2
    have y1e0 : y1 = 0 := by 
      by_contra y1ne0
      push_neg at y1ne0
      apply h at y1ne0
      contradiction
    have y2e0 : y2 = 0 := by 
      by_contra y2ne0
      push_neg at y2ne0
      apply h at y2ne0
      contradiction
    linarith

  rw [l2]

  constructor <;> intro h

  --From left to right, if a = p/q, then we show that the equation has more than one solution.
  rw [irrational_iff_ne_rational]
  intro p q
  by_contra aepoq
  have qne0 : q ≠ 0 := by 
    by_contra qe0
    simp [qe0] at aepoq
    simp [aepoq] at h
    specialize h (2*π)
    simp at h
    have : ¬ π = 0 := by exact pi_ne_zero
    apply h at this
    specialize this 1
    simp at this
  
  specialize h (2* π *q)
  simp [qne0] at h
  have : ¬ π = 0 := by exact pi_ne_zero
  simp [this, aepoq] at h
  specialize h (2*p)
  field_simp at h
  have : 2 * ↑p * π * ↑q = ↑p * (2 * π * ↑q)  := by ring
  simp [this] at h
  specialize h q
  have : ↑q * (2 * π) = 2 * π * ↑q := by ring
  simp [this] at h

  --If a is inrational, then we prove that there is no non-zero solution, since otherwise we can prove that a is rational.
  intro y yne0
  by_contra eq
  obtain ⟨eq1,eq2⟩ := eq
  obtain ⟨n1,hn1⟩ := eq1
  obtain ⟨n2,hn2⟩ := eq2
  rw [← hn2] at hn1
  ring_nf at hn1
  rw [mul_comm] at hn1
  have : π * a * ↑n2 * 2 = π * (a * ↑n2 * 2) := by ring
  rw [this] at hn1
  have : π ≠ 0 := by exact pi_ne_zero
  field_simp [this] at hn1
  have : a = n1 / (2*n2) := by 
    have n2ne0 : n2 ≠ 0 := by 
      by_contra n2e0
      simp [n2e0] at hn2
      simp [hn2] at yne0
    rw [hn1]
    field_simp
    ring
  rw [irrational_iff_ne_rational] at h
  specialize h n1 (2*n2)
  rw [this] at h
  norm_cast at h


