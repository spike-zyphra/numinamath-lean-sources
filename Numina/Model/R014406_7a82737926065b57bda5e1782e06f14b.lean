import Mathlib

open Polynomial

theorem algebra_3173 {x : ℂ} (hx : x ^ 2 - 3 * x - 1 = 0) : 3 * x + 1 / x ^ 2 = 10 := by
  have h1 : x ≠ 0 := by 
    by_contra h
    rw [h] at hx
    norm_num at hx

  have h2 : x ^ 2 = 3 * x + 1 := by
    have h3 : x ^ 2 - 3 * x - 1 = 0 := hx
    calc
      x ^ 2 = x ^ 2 - 3 * x - 1 + 3 * x + 1 := by ring
      _ = 0 + 3 * x + 1 := by rw [h3]
      _ = 3 * x + 1 := by ring

  have h5 : x ^ 2 - 3 * x = 1 := by
    calc
      x ^ 2 - 3 * x = (x ^ 2 - 3 * x - 1) + 1 := by ring
      _ = 0 + 1 := by rw [hx]
      _ = 1 := by ring
  
  have h6 : x * (x - 3) = 1 := by
    calc 
      x * (x - 3) = x ^ 2 - 3 * x := by ring
      _ = 1 := h5

  have h7 : 1 / x = x - 3 := by
    have h8 : x ≠ 0 := h1
    calc 
      1 / x = (x * (x - 3)) / x := by rw [h6]
      _ = (x - 3) := by field_simp [h8]

  have h8 : 1 / x ^ 2 = (x - 3) ^ 2 := by
    calc 
      1 / x ^ 2 = (1 / x) ^ 2 := by field_simp
      _ = (x - 3) ^ 2 := by rw [h7]

  have h9 : (x - 3) ^ 2 = -3 * x + 10 := by
    have h10 : x ^ 2 = 3 * x + 1 := h2
    calc
      (x - 3) ^ 2 = x ^ 2 - 6 * x + 9 := by ring
      _ = (3 * x + 1) - 6 * x + 9 := by rw [h10]
      _ = -3 * x + 10 := by ring

  rw [show 1 / x ^ 2 = -3 * x + 10 by 
      rw [h8]
      rw [h9]
      <;> ring_nf
  ]
  <;> ring_nf