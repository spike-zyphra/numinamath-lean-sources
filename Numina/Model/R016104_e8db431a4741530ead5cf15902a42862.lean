import Mathlib

theorem algebra_102146 {x : ℂ} (hx : x^2 + x + 1 = 0) : x^49 + x^50 + x^51 + x^52 + x^53 = -1 := by
  have h1 : x^2 = -x - 1 := by
    have h2 : x^2 + x + 1 = 0 := hx
    calc
      x^2 = (x^2 + x + 1) - x - 1 := by ring
      _ = 0 - x - 1 := by rw [h2]
      _ = -x - 1 := by ring

  have h2 : x^3 = 1 := by
    calc
      x^3 = x * x^2 := by ring
      _ = x * (-x - 1) := by rw [h1]
      _ = -x^2 - x := by ring_nf
      _ = -(-x - 1) - x := by rw [h1]
      _ = 1 := by ring_nf

  have h4 : ∀ (n : ℕ), x^(3 * n + 1) = x := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      calc 
        x^(3 * (n + 1) + 1) = x ^ (3 * n + 1 + 3) := by ring_nf
        _ = (x ^ (3 * n + 1)) * x^3 := by ring_nf
        _ = x * x^3 := by rw [ih]
        _ = x * 1 := by rw [h2]
        _ = x := by ring

  have h5 : ∀ (n : ℕ), x^(3 * n + 2) = x^2 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      calc 
        x^(3 * (n + 1) + 2) = x ^ (3 * n + 2 + 3) := by ring_nf
        _ = (x ^ (3 * n + 2)) * x^3 := by ring_nf
        _ = x^2 * x^3 := by rw [ih]
        _ = x^2 * 1 := by rw [h2]
        _ = x^2 := by ring

  have h6 : ∀ (n : ℕ), x^(3 * n) = 1 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      calc 
        x^(3 * (n + 1)) = x^(3 * n + 3) := by ring_nf
        _ = (x ^ (3 * n)) * x^3 := by ring_nf
        _ = 1 * x^3 := by rw [ih]
        _ = 1 * 1 := by rw [h2]
        _ = 1 := by ring

  have hx49 : x^49 = x := by
    have h7 : x^49 = x^(3 * 16 + 1) := by norm_num
    rw [h7]
    specialize h4 16
    simpa using h4

  have hx50 : x^50 = x^2 := by
    have h8 : x^50 = x^(3 * 16 + 2) := by norm_num
    rw [h8]
    specialize h5 16
    simpa using h5

  have hx51 : x^51 = 1 := by
    have h9 : x^51 = x^(3 * 17) := by norm_num
    rw [h9]
    specialize h6 17
    simpa using h6

  have hx52 : x^52 = x := by
    have h10 : x^52 = x^(3 * 17 + 1) := by norm_num
    rw [h10]
    specialize h4 17
    simpa using h4

  have hx53 : x^53 = x^2 := by
    have h11 : x^53 = x^(3 * 17 + 2) := by norm_num
    rw [h11]
    specialize h5 17
    simpa using h5

  rw [hx49, hx50, hx51, hx52, hx53]
  rw [h1]
  ring_nf