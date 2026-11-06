import Mathlib

theorem algebra_125739 {a : ℕ → ℤ} (ha1 : a 1 = 1) (ha2 : a 2 = 3) (ha3 : a 3 = 6)
    (hak : ∀ k, a (k + 1) = a k + (k + 1)) (n : ℕ) :
    a n = n * (n + 1) / 2 := by

  have h1 : a 0 = 0 := by 
    have eq1 := hak 0
    norm_num at eq1
    linarith [ha1]

  have h2 : ∀ (n : ℕ), a n = n * (n + 1) / 2 := by
    intro n 
    induction n with
    | zero =>
      simp [h1]
    | succ n ih =>
      have eq3 : a (n + 1) = a n + (n + 1) := by 
        specialize hak n
        simpa using hak
      rw [eq3, ih]
      simp [Int.mul_emod, mul_add, add_mul]
      <;> ring_nf <;> omega
  specialize h2 n
  simpa using h2