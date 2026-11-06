import Mathlib

open Real

/- 3. In the field of real numbers, solve the system of equations


$$

\begin{aligned}
& x^{2}-y z=a, 
& y^{2}-z x=a-1, 
& z^{2}-x y=a+1
\end{aligned}

$$


with a real parameter $a$. Discuss the number of solutions. -/
theorem algebra_273840 (a : ℝ) (x y z : ℝ)
    (h₀ : x^2 - y * z = a) (h₁ : y^2 - z * x = a - 1) (h₂ : z^2 - x * y = a + 1) :
    (∃ x' y' z' : ℝ, x' = x ∧ y' = y ∧ z' = z) ↔ a > 0 ∧ ((x = 1 / (3 * sqrt a) ∧ y = (1 - 3 * a) / (3 * sqrt a) ∧
    z = (1 + 3 * a) / (3 * sqrt a)) ∨ (x = - 1 / (3 * sqrt a) ∧ y = - (1 - 3 * a) / (3 * sqrt a) ∧
    z = - (1 + 3 * a) / (3 * sqrt a))) := by
  constructor

  · intro _
    --subtracting the second equation to the first one gets x^2 - y * z - (y^2 - z * x) = a - (a - 1)
    have eq1 : x^2 - y * z - (y^2 - z * x) = a - (a - 1) := by linarith
    --subtracting the first equation to the third one gets z^2 - x * y - ( x^2 - y * z) = a + 1 - a
    have eq2 : z^2 - x * y - ( x^2 - y * z) = a + 1 - a := by linarith
    --by arithmetic manipulation one derives the system of two equaitons (x - y) * (x + y + z) = 1 and (z - x) * (x + y + z) = 1
    have eq1' : (x - y) * (x + y + z) = 1 := by ring_nf at eq1 ⊢; linarith
    have eq2' : (z - x) * (x + y + z) = 1 := by ring_nf at eq2 ⊢; linarith
    let s := (x + y + z) ^ (-(1 : ℤ))
    --setting s = x + y + z we have that x - y = z - x = s ^ -1
    have den_ne_zero : x + y + z ≠ 0 := by
      by_contra kk
      rw[kk, mul_zero] at eq1'
      linarith
    have hs1 : x - y = s := by simp[s]; rw[inv_eq_one_div]; field_simp; exact eq1'
    have hs2 : z - x = s :=by simp[s]; rw[inv_eq_one_div]; field_simp; exact eq2'
    --find y and z in terms of x and s and rewrite them in the system
    have hs1' : y = x - s := by linarith
    have hs2' : z = x + s := by linarith
    rw[hs1', hs2'] at h₀ h₁ h₂
    ring_nf at h₀ h₁ h₂
    change s ^ 2 = a at h₀
    change -(x * s * 3) + s ^ 2 = -1 + a at h₁
    change x * s * 3 + s ^ 2 = 1 + a at h₂
    rw[h₀] at h₁ h₂
    have s_ne_zero : s ≠ 0 := by 
      by_contra kk
      rw[kk] at hs1
      rw[hs1, zero_mul] at eq1'
      linarith
    --assuming a less than 0 we get that the square root is not defined, so there are no solutions
    by_cases kk : a < 0
    · have _ : s ^ 2 < 0 := by linarith
      have s_non_neg : s ^ 2 ≥ 0 := by exact sq_nonneg s
      exfalso
      linarith
    --if a ≥ 0 then one gets the desired result, finding the system s = ± √ a and 3xs = 1 and then substituting in each equation 
    · push_neg at kk
      rw[← sq_sqrt kk, sq_eq_sq_iff_abs_eq_abs, abs_of_nonneg (sqrt_nonneg a), abs_eq (sqrt_nonneg a)] at h₀
      have a_ne_zero : a ≠ 0 := by
        by_contra contr
        rw[contr] at h₀
        norm_num at h₀
        simp[s] at h₀
        rw[h₀, mul_zero] at eq1'
        linarith
      constructor
      · exact Ne.lt_of_le (id (Ne.symm a_ne_zero)) kk
      --here we distinguish s = √a
      · obtain h01|h02 := h₀
        · rw[h01] at h₂
          have : (3 * sqrt a) ≠ 0 := by rw[mul_ne_zero_iff]; exact ⟨by linarith, by exact (sqrt_ne_zero kk).2 a_ne_zero⟩
          have hx : x = 1 / (3 * sqrt a) := by field_simp; linarith
          rw[h01, hx] at hs1 hs2
          have hy : y = (1 - 3 * a) / (3 * sqrt a) := by 
            field_simp at hs1 ⊢
            rw[← mul_assoc, mul_comm (sqrt a) 3, mul_assoc 3 (sqrt a) (sqrt a), ← sq, sq_sqrt kk] at hs1
            linarith
          have hz : z = (1 + 3 * a) / (3 * sqrt a) := by 
            field_simp at hs2 ⊢
            rw[← mul_assoc (sqrt a) 3 (sqrt a), mul_comm (sqrt a) 3, mul_assoc 3 (sqrt a) (sqrt a), ← sq, sq_sqrt kk] at hs2
            linarith
          left
          exact ⟨hx,hy,hz⟩
        -- s = -√a
        · rw[h02] at h₂
          have : (3 * sqrt a) ≠ 0 := by rw[mul_ne_zero_iff]; exact ⟨by linarith, by exact (sqrt_ne_zero kk).2 a_ne_zero⟩
          have hx' : x = - 1 / (3 * sqrt a) := by field_simp; linarith
          rw[h02, hx'] at hs1 hs2
          have hy' : y = - (1 - 3 * a) / (3 * sqrt a) := by
            field_simp at hs1 ⊢
            rw[← mul_assoc, mul_comm (sqrt a) 3, mul_assoc 3 (sqrt a) (sqrt a), ← sq, sq_sqrt kk] at hs1
            linarith
          have hz' : z = - (1 + 3 * a) / (3 * sqrt a) := by
            field_simp at hs2 ⊢
            rw[← mul_assoc (sqrt a) 3 (sqrt a), mul_comm (sqrt a) 3, mul_assoc 3 (sqrt a) (sqrt a), ← sq, sq_sqrt kk] at hs2
            linarith
          right
          exact ⟨hx',hy',hz'⟩
  . intro h
    obtain ⟨_, _, _, _⟩ := h
    use x, y, z
    use x, y, z