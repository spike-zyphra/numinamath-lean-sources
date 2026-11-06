import Mathlib

theorem algebra_97506 {i : ℂ} (hi : i^2 = -1) : (1 + i)^20 - (1 - i)^20 = 0 := by
  have h1 : (1 + i) ^ 2 = 2 * i := by
    calc
      (1 + i) ^ 2 = (1 + i) * (1 + i) := by ring
      _ = 1 * 1 + 1 * i + i * 1 + i * i := by ring
      _ = 1 + i + i + i^2 := by ring
      _ = 1 + 2 * i + i^2 := by ring
      _ = 1 + 2 * i + (-1) := by rw [hi]
      _ = 2 * i := by ring

  have h2 : (1 + i) ^ 4 = -4 := by
    calc
      (1 + i) ^ 4 = ((1 + i) ^ 2) ^ 2 := by ring
      _ = (2 * i) ^ 2 := by rw [h1]
      _ = 4 * (i ^ 2) := by ring
      _ = 4 * (-1) := by rw [hi]
      _ = -4 := by norm_num

  have h3 : (1 + i) ^ 8 = 16 := by
    calc
      (1 + i) ^ 8 = ((1 + i) ^ 4) ^ 2 := by ring
      _ = (-4) ^ 2 := by rw [h2]
      _ = 16 := by norm_num

  have h4 : (1 + i) ^ 16 = 256 := by
    calc
      (1 + i) ^ 16 = ((1 + i) ^ 8) ^ 2 := by ring
      _ = (16) ^ 2 := by rw [h3]
      _ = 256 := by norm_num

  have h5 : (1 + i) ^ 20 = -1024 := by
    calc
      (1 + i) ^ 20 = (1 + i) ^ 16 * (1 + i) ^ 4 := by ring
      _ = 256 * (-4) := by rw [h4, h2]
      _ = -1024 := by norm_num

  have h6 : (1 - i) ^ 2 = -2 * i := by
    calc
      (1 - i) ^ 2 = (1 - i) * (1 - i) := by ring
      _ = 1 * 1 + 1 * (-i) + (-i) * 1 + (-i) * (-i) := by ring
      _ = 1 - i - i + i^2 := by ring
      _ = 1 - 2 * i + i^2 := by ring
      _ = 1 - 2 * i + (-1) := by rw [hi]
      _ = -2 * i := by ring

  have h7 : (1 - i) ^ 4 = -4 := by
    calc
      (1 - i) ^ 4 = ((1 - i) ^ 2) ^ 2 := by ring
      _ = (-2 * i) ^ 2 := by rw [h6]
      _ = 4 * (i ^ 2) := by ring
      _ = 4 * (-1) := by rw [hi]
      _ = -4 := by norm_num

  have h8 : (1 - i) ^ 8 = 16 := by
    calc
      (1 - i) ^ 8 = ((1 - i) ^ 4) ^ 2 := by ring
      _ = (-4) ^ 2 := by rw [h7]
      _ = 16 := by norm_num

  have h9 : (1 - i) ^ 16 = 256 := by
    calc
      (1 - i) ^ 16 = ((1 - i) ^ 8) ^ 2 := by ring
      _ = (16) ^ 2 := by rw [h8]
      _ = 256 := by norm_num

  have h10 : (1 - i) ^ 20 = -1024 := by
    calc
      (1 - i) ^ 20 = (1 - i) ^ 16 * (1 - i) ^ 4 := by ring
      _ = 256 * (-4) := by rw [h9, h7]
      _ = -1024 := by norm_num

  rw [h5, h10]
  norm_num
  all_goals try tauto