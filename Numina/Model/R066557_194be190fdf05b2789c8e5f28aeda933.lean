import Mathlib

open Real

theorem calculus_10289 {f : ℝ → ℝ} (hf : f = λ x => log (x ^ 2)) :
    deriv f = λ x => 2 / x := by
  rw [hf]
  funext x
  simp [deriv_log, deriv_pow, deriv_id'', mul_comm]
  <;> ring_nf <;> field_simp
  <;> ring
  <;> try field_simp
  <;> try ring_nf
  <;> try field_simp
  <;> try field_simp
  all_goals norm_num
  all_goals try tauto