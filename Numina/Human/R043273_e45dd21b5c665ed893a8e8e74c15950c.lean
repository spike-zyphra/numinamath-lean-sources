import Mathlib

open Complex

/- Of the following complex numbers $z$, which one has the property that $z^5$ has the greatest real part?
$\textbf{(A) }{-}2 \qquad \textbf{(B) }{-}\sqrt3+i \qquad \textbf{(C) }{-}\sqrt2+\sqrt2 i \qquad \textbf{(D) }{-}1+\sqrt3 i\qquad \textbf{(E) }2i$ -/
theorem algebra_94035 :
  (((-2):ℂ)^5).re ≤ ((-√3 + I)^5).re ∧
  ((-√2+√2*I)^5).re ≤ ((-√3 + I)^5).re ∧
  ((-1+√3*I)^5).re ≤ ((-√3 + I)^5).re ∧
  ((2*I)^5).re ≤ ((-√3 + I)^5).re := by
  -- we'll expand all expressions, to do that we'll need the facts that
  -- i^3 = -i, i^5 = i, √3^3 = 3√3, √3^4 = 9, √3^5 = 9√3, √2^3 = 2√2, √2^4 = 4, √2^5 = 4√2
  have hi3 : I^3 = -I := by calc
    I^3 = I^2 * I := by rfl
    _ = - I := by simp
  have hi5 : I^5 = I := by calc
    I^5 = I^4 * I := by rfl
    _ = I := by simp
  have h3_3 : (√3)^3 = 3 * √3 := by calc
    (√3)^3 = (√3)^2 * √3 := by rfl
    _ = 3 * √3 := by simp
  have h3_4 : (√3)^4 = 9 := by calc
    (√3)^4 = (√3)^3 * √3 := by rfl
    _ = 3 * √3 * √3 := by simp [h3_3]
    _ = 9 := by ring_nf; simp; norm_num
  have h3_5 : (√3)^5 = 9 * √3 := by calc
    (√3)^5 = (√3)^4 * √3 := by rfl
    _ = 9 * √3 := by rw [h3_4]
  have h2_3 : (√2)^3 = 2 * √2 := by calc
    (√2)^3 = (√2)^2 * √2 := by rfl
    _ = 2 * √2 := by simp
  have h2_4 : (√2)^4 = 4 := by calc
    (√2)^4 = (√2)^3 * √2 := by rfl
    _ = 2 * √2 * √2 := by simp [h2_3]
    _ = 4 := by ring_nf; simp; norm_num
  have h2_5 : (√2)^5 = 4 * √2 := by calc
    (√2)^5 = (√2)^4 * √2 := by rfl
    _ = 4 * √2 := by rw [h2_4]
  -- now expand all expressions, and replace the real part in target expression
  have : ((-2):ℂ)^5 = -32 := by norm_num
  rw [this]; simp
  have : (-√3 + I)^5 = 16 * √3 + 16 * I := by
    ring_nf
    rw [hi3, hi5]
    norm_cast
    simp [h3_3, h3_4, h3_5]
    ring_nf
  rw [this]; simp
  have : (-√2+√2*I)^5 = 16 * √2 - 16 * √2 * I := by
    ring_nf
    rw [hi3, hi5]
    norm_cast
    simp [h2_3, h2_4, h2_5]
    ring_nf
  rw [this]; simp
  have : (-1+√3*I)^5 = -16 - 16 * √3 * I := by
    ring_nf
    rw [hi3, hi5]
    norm_cast
    simp [h3_3, h3_4, h3_5]
    ring_nf
  rw [this]; simp
  have : (2 * I)^5 = 32 * I := by
    ring_nf
    simp [hi5]
  rw [this]; simp
  -- finally prove each of the inequalities, which are now trivial
  have : 0 ≤ √3 := by simp
  have : 0 ≤ √2 := by simp
  repeat (any_goals constructor)
  . linarith
  . norm_num
  . linarith