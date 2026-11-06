import Mathlib

open Polynomial

theorem algebra_3853 {a : ℂ} (ha : a ^ 2 + a + 1 = 0) :
    a ^ 1989 + a ^ 1990 + a ^ 1994 = 0 := by
  have h1 : a ^ 3 = 1 := by
    have eq1 : a ^ 2 = -a - 1 := by
      have h : a ^ 2 + a + 1 = 0 := ha
      calc
        a ^ 2 = a ^ 2 + a + 1 - a - 1 := by ring
        _ = 0 - a - 1 := by rw [h]
        _ = -a - 1 := by ring
    calc
      a ^ 3 = a * a ^ 2 := by ring 
      _ = a * (-a - 1) := by rw [eq1]
      _ = -a ^ 2 - a := by ring 
      _ = -(-a - 1) - a := by rw [eq1]
      _ = a + 1 - a := by ring 
      _ = 1 := by ring 
  have h2 : a ^ 1989 = 1 := by
    calc
      a ^ 1989 = (a ^ 3) ^ 663 := by ring
      _ = 1 ^ 663 := by rw [h1]
      _ = 1 := by norm_num 
  have h3 : a ^ 1990 = a := by
    calc
      a ^ 1990 = (a ^ 3) ^ 663 * a := by ring 
      _ = 1 ^ 663 * a := by rw [h1]
      _ = 1 * a := by norm_num
      _ = a := by ring 
  have h4 : a ^ 1994 = a ^ 2 := by
    calc
      a ^ 1994 = (a ^ 3) ^ 664 * a ^ 2 := by ring 
      _ = 1 ^ 664 * a ^ 2 := by rw [h1]
      _ = 1 * a ^ 2 := by norm_num 
      _ = a ^ 2 := by ring
  have h5 : 1 + a + a ^ 2 = 0 := by 
    have eq1 : a ^ 2 + a + 1 = 0 := ha 
    calc 
      1 + a + a ^ 2 = a ^ 2 + a + 1 := by ring_nf 
      _ = 0 := by simpa using eq1 
  rw [h2, h3, h4] 
  simpa using h5