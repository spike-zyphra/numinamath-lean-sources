import Mathlib

open Complex

/--
A linear binomial l(z) = Az + B with complex coefficients A and B is given. It is known that the maximum value of |l(z)| on the segment -1 ≤ x ≤ 1, y = 0 is equal to M. Show that for every z, |l(z)| ≤ Mρ, where ρ is the sum of distances from the point P = z to the point Q₁ : z=1 and Q₃ : z=-1.
-/
theorem Other_1846
  (A B : ℂ)
  (l : ℂ → ℂ)
  (hl : l = fun z => A * z + B)
  (M : ℝ)
  (hM : IsLUB {abs (l (.mk p 0)) | (p : Set.Icc (-1:ℝ) 1) } M)
  (z : ℂ) :
  abs (l z) ≤ M * (abs (z - 1) + abs (z + 1)) := by

  -- M is an upper bound of {abs (l (.mk p 0)) | (p : Set.Icc (-1:ℝ) 1) }
  have q := hM.left
  unfold upperBounds at q
  simp at q

  have n1 : (-1:ℂ) = { re := -1, im := 0 } := by apply Complex.ext <;> simp

  -- it suffices to prove the even stronger estimate that 2 |l(z)| ≤ ρM
  calc
    abs (l z) ≤ 2 * abs (l z):= by 
      have : 0 ≤ abs (l z) := AbsoluteValue.nonneg Complex.abs _
      linarith
    _ = 2 * abs (A*z + B) := by simp_rw [hl]
    _ = 2 * abs ((1/2) * ((z+1)*(A+B) + (z-1)*(A-B))) := by ring_nf
    _ = abs ((z+1)*(A+B) + (z-1)*(A-B)) := by
      rw [AbsoluteValue.map_mul Complex.abs]
      norm_num
      ring_nf
    _ = abs ((z+1)*(l 1) - (z-1)*(l (-1))) := by
      congr
      rw [hl]
      dsimp
      ring
    _ ≤ abs ((z+1)*(l 1)) + abs ((z-1)*(l (-1))) := AbsoluteValue.sub_le_add Complex.abs _ _
    _ = abs (z+1)* abs (l 1) + abs ((z-1)*(l (-1))) := by
      congr
      exact AbsoluteValue.map_mul Complex.abs _  _
    _ = abs (z+1)* abs (l 1) + abs (z-1) * abs (l (-1)) := by
      congr
      exact AbsoluteValue.map_mul Complex.abs _ _
    _ ≤ abs (z+1) * M + abs (z-1) * abs (l (-1)) := by
      gcongr
      specialize q 1 (by linarith)
      · exact Complex.abs (l 1)
      · specialize q (by linarith)
        simp only at q
        rw [show (1:ℂ) = { re := 1, im := 0 } by rfl] at q
        simpa using q
    _ ≤ abs (z+1) * M + abs (z-1) * M := by
      gcongr
      specialize q (-1) (by linarith)
      · exact Complex.abs (l (-1))
      · specialize q (by linarith)
        simp only at q
        rw [n1] at q
        simp only [forall_const] at q
        rw [n1]
        exact q
    _ = M * (abs (z-1) + abs (z+1)) := by ring
