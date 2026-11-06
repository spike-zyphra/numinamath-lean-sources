import Mathlib

open Complex

theorem algebra_17085 {z : ℂ} (hz : z ^ 2 + z + 1 = 0) :
    z ^ 97 + z ^ 98 + z ^ 99 + z ^ 100 + z ^ 101 = -1 := by
  have h1 : z ≠ 0 := by
    by_contra h
    rw [h] at hz
    norm_num [pow_two] at hz
  have h2 : z ^ 2 = -z - 1 := by
    have h : z ^ 2 + z + 1 = 0 := hz
    calc
      z ^ 2 = z ^ 2 + z + 1 - z - 1 := by ring_nf
      _ = 0 - z - 1 := by rw [h]
      _ = -z - 1 := by ring_nf
  have h3 : z ^ 3 = 1 := by
    calc
      z ^ 3 = z * z ^ 2 := by ring_nf
      _ = z * (-z - 1) := by rw [h2]
      _ = -z^2 - z := by ring_nf
      _ = -(-z - 1) - z := by rw [h2]
      _ = 1 := by ring_nf
  have h4 : z ^ 97 = z := by
    calc
      z ^ 97 = z ^ (3 * 32 + 1) := by ring_nf
      _ = (z ^ 3) ^ 32 * z := by ring_nf
      _ = 1 ^ 32 * z := by rw [h3]
      _ = 1 * z := by simp
      _ = z := by ring_nf
  have h5 : z ^ 98 = z ^ 2 := by
    calc
      z ^ 98 = z ^ (3 * 32 + 2) := by ring_nf
      _ = (z ^ 3) ^ 32 * z ^ 2 := by ring_nf
      _ = 1 ^ 32 * z ^ 2 := by rw [h3]
      _ = 1 * z ^ 2 := by simp
      _ = z ^ 2 := by ring_nf
  have h6 : z ^ 99 = 1 := by
    calc
      z ^ 99 = z ^ (3 * 33) := by ring_nf
      _ = (z ^ 3) ^ 33 := by ring_nf
      _ = 1 ^ 33 := by rw [h3]
      _ = 1 := by simp
  have h7 : z ^ 100 = z := by
    calc
      z ^ 100 = z ^ (3 * 33 + 1) := by ring_nf
      _ = (z ^ 3) ^ 33 * z := by ring_nf
      _ = 1 ^ 33 * z := by rw [h3]
      _ = 1 * z := by simp
      _ = z := by ring_nf
  have h8 : z ^ 101 = z ^ 2 := by
    calc
      z ^ 101 = z ^ (3 * 33 + 2) := by ring_nf
      _ = (z ^ 3) ^ 33 * z ^ 2 := by ring_nf
      _ = 1 ^ 33 * z ^ 2 := by rw [h3]
      _ = 1 * z ^ 2 := by simp
      _ = z ^ 2 := by ring_nf
  rw [h4, h5, h6, h7, h8]
  rw [h2]
  ring_nf