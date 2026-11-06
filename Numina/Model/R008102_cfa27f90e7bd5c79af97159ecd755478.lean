import Mathlib

theorem algebra_15068 (q n : ℕ) (h : n = q + 7) (h' : 25*q+5*n=455) :
    n=21 := by
  rw [h] at h' 
  omega