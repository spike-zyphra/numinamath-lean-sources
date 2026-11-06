import Mathlib

open Complex

theorem algebra_97790 {F : ℂ → ℂ} (hF : ∀ w, w ≠ I → F w = (w + I) / (w - I))
    (z : ℕ → ℂ) (hz0 : z 0 = 1 / 137 + I) (hzn : ∀ n, z (n + 1) = F (z n)) :
    (z 2002).re + (z 2002).im = 275 := by
  have h1 : z 1 = F (z 0) := hzn 0
  have h2 : z 1 = 1 + 274 * I := by 
    rw [h1, hF (z 0) (by
      intro h
      rw [hz0] at h
      simp [Complex.ext_iff, mul_add, pow_two] at h
      all_goals norm_num at h 
    ), hz0
    ]
    field_simp [Complex.ext_iff, mul_add, pow_two]
    <;> norm_num
    <;> ring
  have h3 : z 2 = F (z 1) := hzn 1
  have h4 : z 2 = 37538 / 37265 + I / 37265 := by 
    rw [h3, hF (z 1) (by
      intro h
      rw [h2] at h
      simp [Complex.ext_iff, mul_add, pow_two] at h
      all_goals norm_num at h 
    ), h2
    ]
    field_simp [Complex.ext_iff, mul_add, pow_two]
    <;> norm_num
    <;> ring
  have h5 : z 3 = F (z 2) := hzn 2
  have h6 : z 3 = 1 / 137 + I := by 
    rw [h5, hF (z 2) (by
      intro h
      rw [h4] at h
      simp [Complex.ext_iff, mul_add, pow_two] at h
      all_goals norm_num at h 
    ), h4
    ]
    field_simp [Complex.ext_iff, mul_add, pow_two]
    <;> norm_num
    <;> ring
  have h9 : ∀ n, z (3 * n + 1) = 1 + 274 * I := by
    intro n
    induction n with
    | zero =>
      simp [h2]
    | succ n ih =>
      have h10 : z (3 * (n + 1) + 1) = z (3 * n + 4) := by
        simp [show 3 * (n + 1) + 1 = 3 * n + 4 by omega]
      have h11 : z (3 * n + 4) = F (z (3 * n + 3)) := hzn (3 * n + 3)
      have h12 : z (3 * n + 3) = F (z (3 * n + 2)) := hzn (3 * n + 2)
      have h13 : z (3 * n + 2) = F (z (3 * n + 1)) := hzn (3 * n + 1)
      rw [h10, h11, h12, h13, ih]
      have h14 : F (1 + 274 * I) = 37538 / 37265 + I / 37265 := by
        rw [hF (1 + 274 * I) (by 
          intro h
          simp [Complex.ext_iff, mul_add, pow_two] at h
          all_goals norm_num at h 
        )]
        field_simp [Complex.ext_iff, mul_add, pow_two]
        <;> norm_num
        <;> ring
      have h15 : F (F (1 + 274 * I)) = 1 / 137 + I := by 
        rw [h14]
        rw [hF (37538 / 37265 + I / 37265) (by
          intro h
          simp [Complex.ext_iff, mul_add, pow_two] at h
          all_goals norm_num at h 
        )]
        field_simp [Complex.ext_iff, mul_add, pow_two]
        <;> norm_num
        <;> ring
      have h16 : F (F (F (1 + 274 * I))) = 1 + 274 * I := by
        rw [h15]
        rw [hF (1 / 137 + I) (by
          intro h
          simp [Complex.ext_iff, mul_add, pow_two] at h
          all_goals norm_num at h 
        )]
        field_simp [Complex.ext_iff, mul_add, pow_two]
        <;> norm_num
        <;> ring
      rw [h16]
  have h2002 : z 2002 = 1 + 274 * I := by 
    have h2002_eq : 2002 = 3 * 667 + 1 := by norm_num
    rw [h2002_eq]
    exact h9 667
  rw [h2002]
  simp
  all_goals norm_num