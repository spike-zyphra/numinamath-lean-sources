import Mathlib

theorem algebra_608040 :
  { f : ℝ → ℝ | ∀ x : ℝ, f (f x * f (1 - x)) = f x ∧ f (f x) = 1 - f x } = {fun _ ↦ 1 / 2} := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume f satisfies both equations, prove f = 1/2
    intro h
    have h1 : ∀ x : ℝ, f (f x * f (1 - x)) = f x := by
      intro x
      have h1 := (h x).1
      simpa using h1
    have h2 : ∀ x : ℝ, f (f x) = 1 - f x := by
      intro x
      have h2 := (h x).2
      simpa using h2
    have eq1 : ∀ x, f (1 - f x) = f x := by
      intro x
      have eq1 : f (f (f x)) = 1 - f (f x) := by
        apply h2
      have eq2 : f (f (f x)) = f (1 - f x) := by
        have eq3 : f (f x) = 1 - f x := h2 x
        rw [eq3]
      have eq3 : f (1 - f x) = 1 - f (f x) := by
        linarith [eq1, eq2]
      have eq4 : f (f x) = 1 - f x := h2 x
      have eq5 : 1 - f (f x) = f x := by
        linarith [eq4]
      linarith [eq3, eq5]
    funext x
    have eq37 : f x = f (1 - x : ℝ) := by
      have eq31 : f (f x * f (1 - x)) = f x := by
        apply h1
      have eq32 : f (f (1 - x) * f (1 - (1 - x : ℝ))) = f (1 - x : ℝ) := by
        apply h1
      have eq33 : 1 - (1 - x : ℝ) = (x : ℝ) := by ring
      rw [eq33] at eq32
      have eq34 : f (f x * f (1 - x)) = f (1 - x : ℝ) := by
        have eq35 : f (f (1 - x) * f x) = f (1 - x : ℝ) := by
          linarith [eq32]
        have eq36 : f (1 - x) * f x = f x * f (1 - x) := by ring
        rw [eq36] at eq35
        linarith [eq35]
      linarith [eq31, eq34]
    have eq30 : f (1 - f x) = f x := by
      apply eq1
    have eq67 : f x = 1 / 2 := by
      have eq58 : f (f x) = 1 - f x := by
        apply h2
      have eq62 : f (1 - f x) = f x := eq30
      have eq78 : f (f (1 - f x : ℝ) * f (1 - (1 - f x : ℝ))) = f (1 - f x : ℝ) := by
        apply h1
      have eq79 : 1 - (1 - f x : ℝ) = (f x : ℝ) := by ring
      rw [eq79] at eq78
      have eq80 : f (f x * (1 - f x : ℝ)) = f x := by
        have eq81 : f (f (1 - f x : ℝ) * f (f x : ℝ)) = f (1 - f x : ℝ) := by
          linarith [eq78]
        have eq82 : f (1 - f x : ℝ) = f x := by
          linarith [eq62]
        have eq83 : f (f x : ℝ) = 1 - f x := by
          have eq84 : f (f x : ℝ) = 1 - f x := by
            apply h2
          linarith [eq84]
        rw [eq82, eq83] at eq81
        nlinarith
      have eq86 : f ( (1 - f x : ℝ) * f x ) = 1 - f x := by
        have eq85 : f (f (f x : ℝ) * f (1 - f x : ℝ)) = f (f x : ℝ) := by
          apply h1
        have eq91 : f (f x : ℝ) = 1 - f x := by
          apply h2
        have eq92 : f (1 - f x : ℝ) = f x := eq62
        rw [eq91, eq92] at eq85
        nlinarith
      have eq93 : (1 - f x : ℝ) * f x = f x * (1 - f x : ℝ) := by ring
      rw [eq93] at eq86
      have eq94 : f x = 1 - f x := by
        linarith [eq80, eq86]
      linarith
    linarith [eq67]
  · -- Assume f = 1/2, prove both equations.
    intro h
    intro x
    simp [h]
    all_goals norm_num