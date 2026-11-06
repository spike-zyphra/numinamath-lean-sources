import Mathlib

/- Given that $\overrightarrow{a}+3\overrightarrow{b}$ is perpendicular to $7\overrightarrow{a}-5\overrightarrow{b}$, and $\overrightarrow{a}-4\overrightarrow{b}$ is perpendicular to $7\overrightarrow{a}-2\overrightarrow{b}$, then the angle between the non-zero vectors $\overrightarrow{a}$ and $\overrightarrow{b}$ is ___          ___. -/
theorem algebra_11449 {a b : ℝ × ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : (a.1 + 3 * b.1, a.2 + 3 * b.2) • (7 * a.1 - 5 * b.1, 7 * a.2 - 5 * b.2) = 0)
    (h2 : (a.1 - 4 * b.1, a.2 - 4 * b.2) • (7 * a.1 - 2 * b.1, 7 * a.2 - 2 * b.2) = 0) :
    Real.arccos ((a.1 * b.1 + a.2 * b.2) / (Real.sqrt (a.1 ^ 2 + a.2 ^ 2) * Real.sqrt (b.1 ^ 2 + b.2 ^ 2))) = 60 * Real.pi / 180 := by

  have eq1 : 7 * (a.1 ^ 2 + a.2 ^ 2) + 16 * (a.1 * b.1 + a.2 * b.2) - 15 * (b.1 ^ 2 + b.2 ^ 2) = 0 := by
    simp [Prod.ext_iff, mul_add, mul_sub] at h1 ⊢
    linarith

  have eq2 : 7 * (a.1 ^ 2 + a.2 ^ 2) - 30 * (a.1 * b.1 + a.2 * b.2) + 8 * (b.1 ^ 2 + b.2 ^ 2) = 0 := by
    simp [Prod.ext_iff, mul_add, mul_sub] at h2 ⊢
    linarith

  have eq3 : 2 * (a.1 * b.1 + a.2 * b.2) = b.1 ^ 2 + b.2 ^ 2 := by
    nlinarith

  have eq4 : a.1 ^ 2 + a.2 ^ 2 = b.1 ^ 2 + b.2 ^ 2 := by
    nlinarith [eq1, eq3]

  have h4 : (a.1 * b.1 + a.2 * b.2) / (Real.sqrt (a.1 ^ 2 + a.2 ^ 2) * Real.sqrt (b.1 ^ 2 + b.2 ^ 2)) = 1 / 2 := by

    have h5 : Real.sqrt (a.1 ^ 2 + a.2 ^ 2) = Real.sqrt (b.1 ^ 2 + b.2 ^ 2) := by 
      rw [show a.1 ^ 2 + a.2 ^ 2 = b.1 ^ 2 + b.2 ^ 2 by linarith [eq4]]

    rw [h5] 
    have hne : (b.1 ^ 2 + b.2 ^ 2) > 0 := by 
      by_contra h 
      push_neg at h
      have : b = (0, 0) := by 
        simp [Prod.ext_iff] at *
        constructor
        · nlinarith
        · nlinarith 
      contradiction

    have h6 : Real.sqrt (b.1 ^ 2 + b.2 ^ 2) * Real.sqrt (b.1 ^ 2 + b.2 ^ 2) = b.1 ^ 2 + b.2 ^ 2 := by
      calc 
        Real.sqrt (b.1 ^ 2 + b.2 ^ 2) * Real.sqrt (b.1 ^ 2 + b.2 ^ 2)
          = (Real.sqrt (b.1 ^ 2 + b.2 ^ 2)) ^ 2 := by ring
        _ = b.1 ^ 2 + b.2 ^ 2 := Real.sq_sqrt (by positivity)

    rw [h6] 
    rw [show a.1 * b.1 + a.2 * b.2 = (b.1 ^ 2 + b.2 ^ 2) / 2 by linarith [eq3]]
    field_simp [hne]
    <;> ring 

  rw [h4] 
  have h8 : Real.arccos (1 / 2) = Real.pi / 3 := by 
    have h9 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three 
    rw [← h9] 
    apply Real.arccos_cos 
    all_goals linarith [Real.pi_pos] 
  rw [h8] 
  ring_nf