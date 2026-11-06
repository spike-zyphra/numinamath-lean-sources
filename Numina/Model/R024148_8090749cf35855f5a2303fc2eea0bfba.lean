import Mathlib

open Finset

theorem algebra_198182 {f : ℝ → ℝ} (hf : f = fun x => (1 + x) / (2 - x))
    (h : f^[13] = f^[31]) : f^[16] = fun x => (x - 1) / x := by
  have h1 := congr_fun h 0
  rw [hf] at h1
  norm_num [Function.iterate_succ_apply', hf] at h1