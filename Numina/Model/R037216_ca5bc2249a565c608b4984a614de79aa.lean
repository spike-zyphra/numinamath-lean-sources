import Mathlib

theorem algebra_10577 {fcond : (ℝ → ℝ) → Prop} (h : fcond = fun f => f 9 = 7) (h1 : ∀ f, fcond f → 2*y = f (2*x) / 2 + 2):
    x + y = 29 / 4:= by

  have h_eq : 2 * y = 11 / 2 := by
    have eq1 := h1 (fun x => (7 : ℝ)) (by
      simp [h]
    )
    norm_num [show (fun x : ℝ => (7 : ℝ)) (2 * x) = (7 : ℝ) by simp] at eq1 ⊢
    linarith

  have eq2 := h1 (fun z => (16 - z : ℝ)) (by
    simp [h]
    all_goals norm_num 
    all_goals try { 
      tauto 
    }
  )
  have h_eq2 : 2 * y = (10 - x : ℝ) := by
    have h_eq2' : (fun z => (16 - z : ℝ)) (2*x) = (16 - 2*x : ℝ) := by
      simp
    rw [h_eq2'] at eq2
    linarith

  have h_eq3 : x = 9 / 2 := by 
    linarith [h_eq, h_eq2]

  have h_eq4 : y = 11 / 4 := by 
    linarith [h_eq]

  linarith [h_eq3, h_eq4]