import Mathlib

theorem algebra_284357 (l t : ℝ) (hl : l > 0) (ht : t > 0)
    (hA : l / t = 45 / (l - t)) (hB : l / t = 30 / (l + t)) :
    l = 180 := by

  have h1 : l * (l - t) = 45 * t := by
    have h1 : l - t ≠ 0 := by
      by_contra h
      have ht' : l = t := by linarith
      rw [ht'] at hA
      field_simp [ht] at hA
      <;> linarith
    have h2 : t ≠ 0 := by linarith
    field_simp [h1, h2] at hA ⊢
    <;> nlinarith [hA]

  have h2 : l * (l + t) = 30 * t := by
    have h1 : l + t ≠ 0 := by
      by_contra h
      have ht' : l = -t := by linarith
      nlinarith [hl, ht, ht']
    have h2 : t ≠ 0 := by linarith
    field_simp [h1, h2] at hB ⊢
    <;> nlinarith [hB]

  have h3 : 2 * l * t + 15 * t = 0 := by
    nlinarith [h1, h2]

  have h4 : 2 * l + 15 = 0 := by
    apply (mul_left_inj' (show t ≠ 0 by linarith)).mp
    linarith

  nlinarith