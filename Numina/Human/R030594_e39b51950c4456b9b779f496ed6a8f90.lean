import Mathlib
/-- Given a $3 \times 3$ square divided into 9 smaller squares,
    and in each small square, an integer is written such that the sums of the elements
    in each row, each column, and each diagonal are equal.
    Prove that this sum cannot be equal to 2008. -/
theorem number_theory_234160 (a : Fin 3 → Fin 3 → ℤ) {s} (h : ∀ i, a i 0 + a i 1 + a i 2 = s)
    (h' : ∀ j, a 0 j + a 1 j + a 2 j = s) (h'' : a 0 0 + a 1 1 + a 2 2 = s)
    (h''' : a 0 2 + a 1 1 + a 2 0 = s) :
    s ≠ 2008 := by
  -- Let $a_{ij}$ be the square, $s$ the sum.
  -- We rewrite the individual equations for the rows to express the last elements
  -- in terms of the previous ones, and get $a_{i2} = s - a_{i1} - a_{i0}$.
  have : a 0 2 = s - a 0 0 - a 0 1 := by linarith[h 0]
  have : a 1 2 = s - a 1 0 - a 1 1 := by linarith[h 1]
  -- $a_{22}$ can also be expressed via column equations, so it equals both
  -- $s - a_{20} - a_{21}$ and $s - a_{02} - a_{12}$.
  have : a 2 2 = s - a 2 0 - a 2 1 := by linarith[h 2]
  have : a 2 2 = s - a 0 2 - a 1 2 := by linarith[h' 2]
  have : a 2 0 = s - a 0 0 - a 1 0 := by linarith[h' 0]
  -- Inserting the terms for $a_{20}$ and $a_{21}$ into the former equation yields
  -- $a_{22} = -s + a_{00} + a_{01} + a_{10} + a_{11}$.
  have : a 2 2 = - s + a 0 0 + a 0 1 + a 1 0 + a 1 1 := by linarith
  -- The diagonal equation $s = a_{00} + a_{11} + a_{22}$ yields
  -- $s = a_{00} + a_{01} - a_{11} + a_{00} + a_{10}$,
  have : s = a 0 0 + a 0 1 - a 1 1 + a 0 0 + a 1 0 := by linarith
  -- while the other one turns to $2s = 2a_{0,0} + 2a_{1,1} + a_{0,1} + a_{1,0}$
  -- (with a bunch of simplifications applied).
  have : 2 * s = 2 * a 0 0 + 2 * a 1 1 + a 0 1 + a 1 0 := by linarith
  -- Subtracting these from another gets us $s = 3 a_{1,1}$,
  have : s = 3 * a 1 1 := by linarith
  have : 3 ∣ s := ⟨_,this⟩
  -- but 2008 is not divisible by 3, contradiction.
  rintro rfl
  norm_num at this