import Mathlib

theorem algebra_20247 (a : ℝ) :
    Set.Infinite {(x, y) : ℝ × ℝ | 3 * x + 2 * y = 8 ∧ 6 * x = 2 * a - 7 - 4 * y} ↔
    a = 23 / 2 := by
  constructor
  · -- Assume the solution set is infinite, prove a = 23/2
    intro h
    by_contra h1
    push_neg at h1
    have h2 : {(x, y) : ℝ × ℝ | 3 * x + 2 * y = 8 ∧ 6 * x = 2 * a - 7 - 4 * y} = ∅ := by
      ext ⟨x, y⟩
      simp
      intro h_eq1 h_eq2
      have eq1 : 3 * x + 2 * y = 8 := h_eq1
      have eq2 : 6 * x = 2 * a - 7 - 4 * y := h_eq2
      have eq3 : 6 * x + 4 * y = 2 * a - 7 := by linarith
      have eq4 : 6 * x + 4 * y = 16 := by
        have eq5 : 3 * x + 2 * y = 8 := eq1
        have eq6 : 6 * x + 4 * y = 2 * (3 * x + 2 * y) := by ring
        rw [eq5] at eq6
        linarith
      have eq7 : 2 * a - 7 = 16 := by linarith [eq3, eq4]
      have eq8 : 2 * a = 23 := by linarith
      have eq9 : a = 23 / 2 := by linarith
      contradiction
    rw [h2] at h
    simp at h
  · -- Assume a = 23/2, prove the solution set is infinite
    intro ha
    rw [ha]
    apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => ((t : ℝ), (8 - 3 * (t : ℝ)) / 2))
    · -- Show the function is injective
      intro t1 t2 ht
      simp [Prod.ext_iff] at ht ⊢
      linarith
    · -- Show that for all t, f(t) is in the solution set
      intro t
      simp [Prod.ext_iff]
      all_goals
        constructor
        · -- First equation
          ring_nf
        · -- Second equation
          ring_nf