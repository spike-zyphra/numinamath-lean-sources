import Mathlib
open Real

theorem algebra_96016 {x y t : ℝ} (ht : t > 0) (ht1 : t ≠ 1)
(hx : x = t ^ ((1 : ℝ) / (t - 1))) (hy : y = t ^ (t / (t - 1))) :
y ^ x = x ^ y := by
  rw [hx, hy]
  have ht2 : t - 1 ≠ 0 := by
    by_contra h
    have : t = 1 := by linarith
    tauto
  have h1 : ((t : ℝ) ^ (t / (t - 1) : ℝ)) ^ ((t : ℝ) ^ (1 / (t - 1) : ℝ)) =
    (t : ℝ) ^ ((t / (t - 1) : ℝ) * ((t : ℝ) ^ (1 / (t - 1) : ℝ))) := by
    rw [← Real.rpow_mul]
    ring_nf
    all_goals linarith
  have h2 : ((t : ℝ) ^ (1 / (t - 1) : ℝ)) ^ ((t : ℝ) ^ (t / (t - 1) : ℝ)) =
    (t : ℝ) ^ ((1 / (t - 1) : ℝ) * ((t : ℝ) ^ (t / (t - 1) : ℝ))) := by
    rw [← Real.rpow_mul]
    ring_nf
    all_goals linarith
  rw [h1, h2]
  have h3 : (t / (t - 1) : ℝ) * ((t : ℝ) ^ (1 / (t - 1) : ℝ)) =
    (1 / (t - 1) : ℝ) * ((t : ℝ) ^ (t / (t - 1) : ℝ)) := by
    have ht4 : (t / (t - 1) : ℝ) * ((t : ℝ) ^ (1 / (t - 1) : ℝ)) =
      (t : ℝ) ^ (t / (t - 1) : ℝ) / (t - 1 : ℝ) := by
      have ht5 : (t / (t - 1) : ℝ) * ((t : ℝ) ^ (1 / (t - 1) : ℝ)) =
        (t * ((t : ℝ) ^ (1 / (t - 1) : ℝ))) / (t - 1 : ℝ) := by
        field_simp [ht2]
      rw [ht5]
      have ht6 : (t * ((t : ℝ) ^ (1 / (t - 1) : ℝ))) / (t - 1 : ℝ) =
        (t : ℝ) ^ (t / (t - 1) : ℝ) / (t - 1 : ℝ) := by
        have ht7 : (t * ((t : ℝ) ^ (1 / (t - 1) : ℝ))) = (t : ℝ) ^ (t / (t - 1) : ℝ) := by
          have ht8 : (t : ℝ) ^ (t / (t - 1) : ℝ) = (t : ℝ) ^ (1 + (1 / (t - 1) : ℝ)) := by
            field_simp [ht2]
            <;> ring_nf 
          rw [ht8]
          rw [show (t : ℝ) ^ (1 + (1 / (t - 1) : ℝ)) = (t : ℝ) ^ (1 : ℝ) * (t : ℝ) ^ (1 / (t - 1) : ℝ) by
            rw [← Real.rpow_add]
            ring_nf
            all_goals linarith
          ]
          simp
        rw [ht7]
      linarith [ht6]
    have ht9 : (1 / (t - 1) : ℝ) * ((t : ℝ) ^ (t / (t - 1) : ℝ)) =
      (t : ℝ) ^ (t / (t - 1) : ℝ) / (t - 1 : ℝ) := by
      field_simp [ht2]
    rw [ht4, ht9]
  rw [h3]