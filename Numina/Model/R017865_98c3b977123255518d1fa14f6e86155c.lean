import Mathlib

theorem algebra_253412 (a b c : ℂ) :
    Complex.abs a ^ 2 + Complex.abs b ^ 2 + Complex.abs c ^ 2 + Complex.abs (a + b + c) ^ 2 =
    Complex.abs (a + b) ^ 2 + Complex.abs (b + c) ^ 2 + Complex.abs (a + c) ^ 2 := by
  have h1 : Complex.abs a = Real.sqrt (a.re ^ 2 + a.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
    <;> simp [pow_two]
    <;> ring
  have h2 : Complex.abs b = Real.sqrt (b.re ^ 2 + b.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
    <;> simp [pow_two]
    <;> ring
  have h3 : Complex.abs c = Real.sqrt (c.re ^ 2 + c.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
    <;> simp [pow_two]
    <;> ring
  have h4 : Complex.abs (a + b + c) = Real.sqrt ((a + b + c).re ^ 2 + (a + b + c).im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
    <;> simp [pow_two]
    <;> ring
  have h5 : Complex.abs (a + b) = Real.sqrt ((a + b).re ^ 2 + (a + b).im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
    <;> simp [pow_two]
    <;> ring
  have h6 : Complex.abs (b + c) = Real.sqrt ((b + c).re ^ 2 + (b + c).im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
    <;> simp [pow_two]
    <;> ring
  have h7 : Complex.abs (a + c) = Real.sqrt ((a + c).re ^ 2 + (a + c).im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
    <;> simp [pow_two]
    <;> ring
  rw [h1, h2, h3, h4, h5, h6, h7]
  have h8 : (a + b + c).re = a.re + b.re + c.re := by
    simp
  have h9 : (a + b + c).im = a.im + b.im + c.im := by
    simp
  have h10 : (a + b).re = a.re + b.re := by
    simp
  have h11 : (a + b).im = a.im + b.im := by
    simp
  have h12 : (b + c).re = b.re + c.re := by
    simp
  have h13 : (b + c).im = b.im + c.im := by
    simp
  have h14 : (a + c).re = a.re + c.re := by
    simp
  have h15 : (a + c).im = a.im + c.im := by
    simp
  rw [h8, h9, h10, h11, h12, h13, h14, h15]
  have h16 : Real.sqrt (a.re ^ 2 + a.im ^ 2) ^ 2 = a.re ^ 2 + a.im ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h17 : Real.sqrt (b.re ^ 2 + b.im ^ 2) ^ 2 = b.re ^ 2 + b.im ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h18 : Real.sqrt (c.re ^ 2 + c.im ^ 2) ^ 2 = c.re ^ 2 + c.im ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h19 : Real.sqrt ((a.re + b.re + c.re) ^ 2 + (a.im + b.im + c.im) ^ 2) ^ 2 =
      (a.re + b.re + c.re) ^ 2 + (a.im + b.im + c.im) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h20 : Real.sqrt ((a.re + b.re) ^ 2 + (a.im + b.im) ^ 2) ^ 2 =
      (a.re + b.re) ^ 2 + (a.im + b.im) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h21 : Real.sqrt ((b.re + c.re) ^ 2 + (b.im + c.im) ^ 2) ^ 2 =
      (b.re + c.re) ^ 2 + (b.im + c.im) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h22 : Real.sqrt ((a.re + c.re) ^ 2 + (a.im + c.im) ^ 2) ^ 2 =
      (a.re + c.re) ^ 2 + (a.im + c.im) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  rw [h16, h17, h18, h19, h20, h21, h22]
  ring_nf