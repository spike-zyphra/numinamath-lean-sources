import Mathlib

open Complex

/- 6. Given complex numbers $z_{1}, z_{2}$ satisfy $\left|z_{1}+z_{2}\right|=20,\left|z_{1}^{2}+z_{2}^{2}\right|=16$, then the minimum value of $\left|z_{1}^{3}+z_{2}^{3}\right|$ is -/

theorem algebra_253416 : IsLeast {‖z1^3 + z2^3‖ | (z1 : ℂ) (z2 : ℂ) (_ : ‖z1 + z2‖ = 20)
    (_ : ‖z1^2 + z2^2‖ = 16)} 3520 := by
  constructor
  -- first proving 3520 belongs to set
  . simp
    -- use 10 + √92 * I and 10 - √92 * I as values for z1 z2
    use 10 + I * √92, 10 - I * √92
    -- just use ring and simp to show the equations
    and_intros
    . ring_nf
      simp
      norm_cast
      simp
      norm_num
    . ring_nf
      simp
    . ring_nf
      simp
      norm_cast
      simp
      norm_num
  -- to prove 3520 is a lower bound, assume z1 z2
  . rintro x ⟨z1, z2, h_sum, h_sum_sq, hx⟩
    rw [← hx]
    -- write z1^3 + z2^3 using z1 + z2 and z1^2 + z2^2
    convert_to 3520 ≤ ‖(z1 + z2) * (3 * (z1^2 + z2^2) - (z1 + z2)^2) * (1/2)‖
    . congr
      ring
    -- flip the subtractin direction and plug in h_sum
    simp [-norm_eq_abs, h_sum]
    rw [norm_sub_rev]
    -- the target is actually ‖a‖ - ‖b‖ ≤ ‖a - b‖
    suffices 352 ≤ ‖(z1 + z2) ^ 2 - 3 * (z1 ^ 2 + z2 ^ 2)‖  by linarith
    simp
    convert norm_sub_norm_le ((z1 + z2) ^ 2) (3 * (z1 ^ 2 + z2 ^ 2))
    -- plug in h_sum and h_sum_sq
    simp [h_sum, h_sum_sq]
    norm_num