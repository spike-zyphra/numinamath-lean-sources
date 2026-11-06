import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_270541 {c : ℝ} (hc : ∀ x ∈ Ioo (-1/4) (1/4), arctan ((2-2*x)/(1+4*x)) + c = -arctan ((2-2*x)/(1+4*x)) - c) :
    c = -arctan 2 := by
  have h1 := hc 0 (by norm_num [mem_Ioo])
  norm_num at h1 
  linarith [h1]