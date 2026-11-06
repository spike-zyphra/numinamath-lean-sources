import Mathlib

/- Given that $\cos x - 4 \sin x = 1,$ find all possible values of $\sin x + 4 \cos x.$ -/
theorem calculus_14838 (x : ℝ) (h : Real.cos x - 4 * Real.sin x = 1) :
  Real.sin x + 4 * Real.cos x = -4 ∨ Real.sin x + 4 * Real.cos x = 4 := by
  -- cosx-4sinx=1, square both sides, cos^2 - 2cos+1 = 16 sin^2 = 16-16 cos^2, therefore cosx is determined.
  let c := Real.cos x
  have c_def: c = Real.cos x := rfl
  let s := Real.sin x
  have s_def: s = Real.sin x := rfl
  have hcs: c^2 + s^2 = 1 := by
    rw [c_def, s_def]; simp
  have h1: c = 1 ∨ c = - 15/17 := by
    rw [← c_def, ← s_def] at h
    have ht1: c-1 = 4*s := by
      rw [← h]; ring
    have ht2: (c-1)^2 = (4*s)^2 := by
      rw [ht1]
    have ht3: c^2-2*c+1 = 16-16*c^2 := by
      have hh1: c^2-2*c+1 = (c-1)^2 := by ring
      have hh2: c^2 = 1-s^2 := by
        rw [c_def, s_def]
        apply Real.cos_sq'
      rw [hh1, hh2, ht2]; ring
    -- c^2-2c+1=16-16c^2, so 17c^2-2c-15=0
    have ht4: 17*c^2-2*c-15 = 0 := by
      have hh1: (15:ℝ) = (c^2-2*c+1) +15 - (c^2-2*c+1) := by ring
      rw [hh1]; nth_rw 2 [ht3]; ring
    -- factorization. 17c^2-2c-15 = (17c+15)(c-1) = 0
    have ht5: 17*c^2-2*c-15 = (17*c+15)*(c-1) := by ring
    rw [ht5] at ht4
    have ht6 := mul_eq_zero.mp ht4
    rcases ht6 with hl | hr
    · right; linarith [hl]
    · left; linarith [hr]
  -- sin^2+cos^2=1
  have h2: s^2 = 1-c^2 := by
    rw [← hcs]; ring
  -- c = 1 or c = - 15/17, we calculate s+4c in these two cases.
  rcases h1 with c1 | c1517
  · have hs: s = 0 := by
    -- when c=1, we solve s=0.
      rw [c1] at h2; simp at h2
      apply h2
    rw [← c_def, ← s_def, c1, hs]; simp
  · have hs: s = -8/17 := by
    -- when c = -15/17, we solve s from h:c-4s=1
      rw [← c_def, ← s_def, c1517] at h
      linarith [h]
    -- substitute c = -15/17 and s = -8/17, s+4c = (-8-15x4)/17 = -68/17 = -4
    rw [← c_def, ← s_def, c1517, hs]; left; field_simp; ring