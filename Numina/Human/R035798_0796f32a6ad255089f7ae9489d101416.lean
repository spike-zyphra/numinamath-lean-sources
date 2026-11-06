import Mathlib

/- Compute the positive real number $x$ satisfying

$$
x^{\left(2 x^{6}\right)}=3
$$ -/
theorem algebra_609783 :
  {x | x > 0 ∧ x ^ (2 * x ^ 6) = 3} = {(3 : ℝ) ^ ((1 : ℝ) / 6)} := by
  ext x
  simp
  constructor
  swap
  {
    rintro rfl
    use by positivity
    rw [← Real.rpow_mul_natCast (by simp) _ 6,
        ← Real.rpow_mul (by simp)]
    norm_num
  }
  rintro ⟨hx, h⟩
  let t := x ^ 6
  suffices H : t = 3 by
    simp [t] at H
    rw [← H,
        ← Real.rpow_natCast_mul (by positivity) 6 _]
    simp
  apply_fun (· ^ 3) at h
  rw [← Real.rpow_mul_natCast (by positivity) _ 3] at h
  ring_nf at h
  rw [mul_comm,
      show (6 : ℝ) = (6 : ℕ) by simp,
      Real.rpow_natCast_mul (by positivity) 6 _] at h
  change t ^ t = 27 at h
  have htpos : t > 0 := by positivity
  clear_value t
  clear x hx
  rcases le_or_gt t 1 with ht | ht
  . have H : t ^ t ≤ 1 := Real.rpow_le_one (le_of_lt htpos) ht (le_of_lt htpos)
    norm_num [h] at H
  . have H : StrictMonoOn (fun (x : ℝ) ↦ x ^ x) (Set.Ioi 1) := by
      intro x hx y hy hxy
      simp at hx hy ⊢
      calc x ^ x
        _ < x ^ y := (Real.rpow_lt_rpow_left_iff hx).mpr hxy
        _ < y ^ y := (Real.rpow_lt_rpow_iff (by linarith) (by linarith) (by linarith)).mpr hxy
    rw [show 27 = (3 : ℝ) ^ (3 : ℝ) by norm_num] at h
    exact H.injOn ht (by simp) h
