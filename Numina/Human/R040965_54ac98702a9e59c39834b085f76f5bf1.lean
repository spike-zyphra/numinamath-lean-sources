import Mathlib
set_option maxRecDepth 10000

/--
Let `p = 101` and `r = 10`. Define the integer

  E = (-1) ^ (p * r) * ((-2)^r - 1)

Then we prove that `E ≡ 13 mod 101`.
--/
theorem Number_Theory_609424 :
  ∃ E : ℤ, E = (-1) ^ (101 * 10) * ((-2)^10 - 1) ∧ E % 101 = 13 := by
  let p := 101
  let r := 10
  let base : ℤ := -2

  let sign : ℤ := (-1) ^ (p * r)
  let power : ℤ := base ^ r
  let diff : ℤ := power - 1
  let E : ℤ := sign * diff

  -- Step 1: Prove intermediate values
  have h_sign : sign = 1 := by norm_num
  have h_power : power = 1024 := by norm_num
  have h_diff : diff = 1023 := by
    change power - 1 = 1023
    rw [h_power]
    norm_num
  have h_E : E = 1023 := by
    change sign * diff = 1023
    rw [h_sign, h_diff]
    norm_num

  -- Step 2: Prove the final modulo result
  have h_mod : E % 101 = 13 := by
    rw [h_E]
    norm_num

  exact ⟨E, h_E, h_mod⟩
