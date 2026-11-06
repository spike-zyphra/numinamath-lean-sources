import Mathlib

open Real


theorem algebra_308326 {f: ℝ → ℝ} (hf: ∀ x, f (1 + cos x) = sin x ^ 2 + cos x - 1):
    ∀ x, x ∈ Set.Icc 0 1 → f x = - x ^ 2 + 3 * x - 2 := by
    intro x hx
    rw [Set.mem_Icc] at hx
    set y := arccos (x - 1)
    have eq42 : 1 + cos y = x := by
      have h2 : cos y = x - 1 := by 
        have h31 : -1 ≤ x - 1 := by linarith [hx.1]
        have h32 : x - 1 ≤ 1 := by linarith [hx.2]
        have eq3 : cos (arccos (x - 1)) = x - 1 := by 
          apply Real.cos_arccos h31 h32
        rw [show y = arccos (x - 1) by rfl] at *
        exact eq3
      linarith
  
    have eq3 : f x = -x ^ 2 + 3 * x - 2 := by

      have eq4 : f x = sin y ^ 2 + cos y - 1 := by

        have eq20 : f (1 + cos y) = sin y ^ 2 + cos y - 1 := hf y
        have eq4 : f x = sin y ^ 2 + cos y - 1 := by
          rw [show 1 + cos y = x by linarith [eq42]] at eq20
          linarith

        exact eq4

      have eq7 : sin y ^ 2 = 1 - (x - 1) ^ 2 := by
        have eq8 : sin y ^ 2 = 1 - cos y ^ 2 := by
          have eq9 : sin y ^ 2 + cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
          linarith

        have eq8a : cos y = x - 1 := by 
          have h31 : -1 ≤ x - 1 := by linarith [hx.1]
          have h32 : x - 1 ≤ 1 := by linarith [hx.2]
          have eq3 : cos (arccos (x - 1)) = x - 1 := by 
            apply Real.cos_arccos h31 h32
          rw [show y = arccos (x - 1) by rfl] at *
          exact eq3

        rw [eq8]
        all_goals 
          rw [eq8a]
          <;> nlinarith

      have h2b : cos y = x - 1 := by 
        have h31 : -1 ≤ x - 1 := by linarith [hx.1]
        have h32 : x - 1 ≤ 1 := by linarith [hx.2]
        have eq3 : cos (arccos (x - 1)) = x - 1 := by 
          apply Real.cos_arccos h31 h32
        rw [show y = arccos (x - 1) by rfl] at *
        exact eq3

      rw [eq4]
      rw [eq7, h2b]
      nlinarith [sq_nonneg (x - 1), sq_nonneg (x - 0)]

    exact eq3