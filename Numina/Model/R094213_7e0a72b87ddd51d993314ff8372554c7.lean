import Mathlib

open Real

theorem algebra_231786 {f h : ℝ} (hf : 0 < f) (hh : 0 < h) (h₁ : log f = log h) : f = h := by 
  have h2 : f = h := by
    exact log_injOn_pos (Set.mem_Ioi.mpr hf) (Set.mem_Ioi.mpr hh) h₁
  exact h2