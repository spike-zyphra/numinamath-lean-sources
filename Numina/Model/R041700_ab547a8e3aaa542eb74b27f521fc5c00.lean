import Mathlib

open Complex

theorem algebra_10333 : I^11 + I^16 + I^21 + I^26 + I^31 = -I := by
  have h1 : I ^ 11 = -I := by
    have h2 : I ^ 3 = -I := by
      calc
        I ^ 3 = I ^ 2 * I := by ring
        _ = (-1) * I := by simp [I_sq]
        _ = -I := by ring
    calc
      I ^ 11 = I ^ (8 + 3) := by ring
      _ = (I ^ 4) ^ 2 * I ^ 3 := by ring
      _ = (1) ^ 2 * I ^ 3 := by simp [I_sq]
      _ = (1) ^ 2 * (-I) := by rw [h2]
      _ = -I := by ring

  have h2 : I ^ 16 = 1 := by
    calc
      I ^ 16 = (I ^ 4) ^ 4 := by ring
      _ = (1) ^ 4 := by simp [I_sq]
      _ = 1 := by norm_num

  have h3 : I ^ 21 = I := by
    calc
      I ^ 21 = I ^ (20 + 1) := by ring
      _ = (I ^ 4) ^ 5 * I := by ring
      _ = (1) ^ 5 * I := by simp [I_sq]
      _ = (1 : ℂ) * I := by ring_nf
      _ = I := by ring

  have h4 : I ^ 26 = -1 := by
    calc
      I ^ 26 = I ^ (24 + 2) := by ring
      _ = (I ^ 4) ^ 6 * I ^ 2 := by ring
      _ = (1) ^ 6 * I ^ 2 := by simp [I_sq]
      _ = (1) ^ 6 * (-1) := by simp [I_sq]
      _ = -1 := by ring

  have h5 : I ^ 31 = -I := by
    have h6 : I ^ 3 = -I := by
      calc
        I ^ 3 = I ^ 2 * I := by ring
        _ = (-1) * I := by simp [I_sq]
        _ = -I := by ring
    calc
      I ^ 31 = I ^ (28 + 3) := by ring
      _ = (I ^ 4) ^ 7 * I ^ 3 := by ring
      _ = (1) ^ 7 * I ^ 3 := by simp [I_sq]
      _ = (1) ^ 7 * (-I) := by rw [h6]
      _ = -I := by ring

  rw [h1, h2, h3, h4, h5]
  ring