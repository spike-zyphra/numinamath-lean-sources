import Mathlib

theorem algebra_603986 {x a : ℝ} (hx : x ≠ 0) (h : x + 1 / x = a) :
    x ^ 13 + 1 / x ^ 13 = a ^ 13 - 13 * a ^ 11 + 65 * a ^ 9 - 156 * a ^ 7 + 182 * a ^ 5 - 91 * a ^ 3 + 13 * a := by
  have h1 : x ^ 2 + 1 / x ^ 2 = (a ^ 2 - 2) := by
    calc
      x ^ 2 + 1 / x ^ 2 = (x + 1 / x) ^ 2 - 2 := by 
        field_simp
        <;> ring
      _ = a ^ 2 - 2 := by 
        rw [h]

  have h2 : x ^ 3 + 1 / x ^ 3 = a ^ 3 - 3 * a := by
    calc
      x ^ 3 + 1 / x ^ 3 = (x + 1 / x) * (x ^ 2 + 1 / x ^ 2) - (x + 1 / x) := by 
        field_simp
        <;> ring
      _ = a * (a ^ 2 - 2) - a := by 
        rw [h1, h]
      _ = a ^ 3 - 3 * a := by 
        ring

  have h3 : x ^ 4 + 1 / x ^ 4 = a ^ 4 - 4 * a ^ 2 + 2 := by
    calc
      x ^ 4 + 1 / x ^ 4 = (x + 1 / x) * (x ^ 3 + 1 / x ^ 3) - (x ^ 2 + 1 / x ^ 2) := by 
        field_simp
        <;> ring
      _ = a * (a ^ 3 - 3 * a) - (a ^ 2 - 2) := by 
        rw [h2, h1, h]
      _ = a ^ 4 - 4 * a ^ 2 + 2 := by 
        ring

  have h4 : x ^ 5 + 1 / x ^ 5 = a ^ 5 - 5 * a ^ 3 + 5 * a := by
    calc
      x ^ 5 + 1 / x ^ 5 = (x + 1 / x) * (x ^ 4 + 1 / x ^ 4) - (x ^ 3 + 1 / x ^ 3) := by 
        field_simp
        <;> ring
      _ = a * (a ^ 4 - 4 * a ^ 2 + 2) - (a ^ 3 - 3 * a) := by 
        rw [h3, h2, h]
      _ = a ^ 5 - 5 * a ^ 3 + 5 * a := by 
        ring

  have h5 : x ^ 6 + 1 / x ^ 6 = a ^ 6 - 6 * a ^ 4 + 9 * a ^ 2 - 2 := by
    calc
      x ^ 6 + 1 / x ^ 6 = (x + 1 / x) * (x ^ 5 + 1 / x ^ 5) - (x ^ 4 + 1 / x ^ 4) := by 
        field_simp
        <;> ring
      _ = a * (a ^ 5 - 5 * a ^ 3 + 5 * a) - (a ^ 4 - 4 * a ^ 2 + 2) := by 
        rw [h4, h3, h]
      _ = a ^ 6 - 6 * a ^ 4 + 9 * a ^ 2 - 2 := by 
        ring

  have h6 : x ^ 7 + 1 / x ^ 7 = a ^ 7 - 7 * a ^ 5 + 14 * a ^ 3 - 7 * a := by
    calc
      x ^ 7 + 1 / x ^ 7 = (x + 1 / x) * (x ^ 6 + 1 / x ^ 6) - (x ^ 5 + 1 / x ^ 5) := by 
        field_simp
        <;> ring
      _ = a * (a ^ 6 - 6 * a ^ 4 + 9 * a ^ 2 - 2) - (a ^ 5 - 5 * a ^ 3 + 5 * a) := by 
        rw [h5, h4, h]
      _ = a ^ 7 - 7 * a ^ 5 + 14 * a ^ 3 - 7 * a := by 
        ring

  have h7 : x ^ 8 + 1 / x ^ 8 = a ^ 8 - 8 * a ^ 6 + 20 * a ^ 4 - 16 * a ^ 2 + 2 := by
    calc
      x ^ 8 + 1 / x ^ 8 = (x + 1 / x) * (x ^ 7 + 1 / x ^ 7) - (x ^ 6 + 1 / x ^ 6) := by 
        field_simp
        <;> ring
      _ = a * (a ^ 7 - 7 * a ^ 5 + 14 * a ^ 3 - 7 * a) - (a ^ 6 - 6 * a ^ 4 + 9 * a ^ 2 - 2) := by 
        rw [h6, h5, h]
      _ = a ^ 8 - 8 * a ^ 6 + 20 * a ^ 4 - 16 * a ^ 2 + 2 := by 
        ring

  have h8 : x ^ 9 + 1 / x ^ 9 = a ^ 9 - 9 * a ^ 7 + 27 * a ^ 5 - 30 * a ^ 3 + 9 * a := by
    calc
      x ^ 9 + 1 / x ^ 9 = (x + 1 / x) * (x ^ 8 + 1 / x ^ 8) - (x ^ 7 + 1 / x ^ 7) := by 
        field_simp
        <;> ring
      _ = a * (a ^ 8 - 8 * a ^ 6 + 20 * a ^ 4 - 16 * a ^ 2 + 2) - (a ^ 7 - 7 * a ^ 5 + 14 * a ^ 3 - 7 * a) := by 
        rw [h7, h6, h]
      _ = a ^ 9 - 9 * a ^ 7 + 27 * a ^ 5 - 30 * a ^ 3 + 9 * a := by 
        ring

  have h9 : x ^ 10 + 1 / x ^ 10 = a ^ 10 - 10 * a ^ 8 + 35 * a ^ 6 - 50 * a ^ 4 + 25 * a ^ 2 - 2 := by
    calc
      x ^ 10 + 1 / x ^ 10 = (x + 1 / x) * (x ^ 9 + 1 / x ^ 9) - (x ^ 8 + 1 / x ^ 8) := by 
        field_simp
        <;> ring
      _ = a * (a ^ 9 - 9 * a ^ 7 + 27 * a ^ 5 - 30 * a ^ 3 + 9 * a) - (a ^ 8 - 8 * a ^ 6 + 20 * a ^ 4 - 16 * a ^ 2 + 2) := by 
        rw [h8, h7, h]
      _ = a ^ 10 - 10 * a ^ 8 + 35 * a ^ 6 - 50 * a ^ 4 + 25 * a ^ 2 - 2 := by 
        ring

  have h10 : x ^ 11 + 1 / x ^ 11 = a ^ 11 - 11 * a ^ 9 + 44 * a ^ 7 - 77 * a ^ 5 + 55 * a ^ 3 - 11 * a := by
    calc
      x ^ 11 + 1 / x ^ 11 = (x + 1 / x) * (x ^ 10 + 1 / x ^ 10) - (x ^ 9 + 1 / x ^ 9) := by 
        field_simp
        <;> ring
      _ = a * (a ^ 10 - 10 * a ^ 8 + 35 * a ^ 6 - 50 * a ^ 4 + 25 * a ^ 2 - 2) - (a ^ 9 - 9 * a ^ 7 + 27 * a ^ 5 - 30 * a ^ 3 + 9 * a) := by 
        rw [h9, h8, h]
      _ = a ^ 11 - 11 * a ^ 9 + 44 * a ^ 7 - 77 * a ^ 5 + 55 * a ^ 3 - 11 * a := by 
        ring

  have h11 : x ^ 12 + 1 / x ^ 12 = a ^ 12 - 12 * a ^ 10 + 54 * a ^ 8 - 112 * a ^ 6 + 105 * a ^ 4 - 36 * a ^ 2 + 2 := by
    calc
      x ^ 12 + 1 / x ^ 12 = (x + 1 / x) * (x ^ 11 + 1 / x ^ 11) - (x  ^ 10 + 1 / x ^ 10) := by 
        field_simp
        <;> ring
      _ = a * (a ^ 11 - 11 * a ^ 9 + 44 * a ^ 7 - 77 * a ^ 5 + 55 * a ^ 3 - 11 * a) - (a ^ 10 - 10 * a ^ 8 + 35 * a ^ 6 - 50 * a ^ 4 + 25 * a ^ 2 - 2) := by 
        rw [h10, h9, h]
      _ = a ^ 12 - 12 * a ^ 10 + 54 * a ^ 8 - 112 * a ^ 6 + 105 * a ^ 4 - 36 * a ^ 2 + 2 := by 
        ring

  have h12 : x ^ 13 + 1 / x ^ 13 = a ^ 13 - 13 * a ^ 11 + 65 * a ^ 9 - 156 * a ^ 7 + 182 * a ^ 5 - 91 * a ^ 3 + 13 * a := by
    calc
      x ^ 13 + 1 / x ^ 13 = (x + 1 / x) * (x ^ 12 + 1 / x ^ 12) - (x ^ 11 + 1 / x ^ 11) := by 
        field_simp
        <;> ring
      _ = a * (a ^ 12 - 12 * a ^ 10 + 54 * a ^ 8 - 112 * a ^ 6 + 105 * a ^ 4 - 36 * a ^ 2 + 2) - (a ^ 11 - 11 * a ^ 9 + 44 * a ^ 7 - 77 * a ^ 5 + 55 * a ^ 3 - 11 * a) := by 
        rw [h11, h10, h]
      _ = a ^ 13 - 13 * a ^ 11 + 65 * a ^ 9 - 156 * a ^ 7 + 182 * a ^ 5 - 91 * a ^ 3 + 13 * a := by 
        ring

  linarith [h12]