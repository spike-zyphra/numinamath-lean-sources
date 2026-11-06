import Mathlib

open SignType

/- ## Task 32/65

Show that the two inequalities

$$
x y z(x+y+z)>0 \quad \text { and } \quad x y+y z+x z>0
$$

with $x ; y ; z \neq 0$ hold if and only if $\operatorname{sgn} x=\operatorname{sgn} y=\operatorname{sgn} z$.
Here, $\operatorname{sgn} a=0$ if $a=0$, $\operatorname{sgn} a=1$ if $a>0$, and $\operatorname{sgn} a=-1$ if $a<0$. -/
theorem inequalities_148219 (x y z : ℝ) (xnz : x ≠ 0) (ynz : y ≠ 0) (znz : z ≠ 0) :
    (x * y * z * (x + y + z) > 0 ∧ x * y + y * z + x * z > 0) ↔
    (sign x = sign y ∧ sign y = sign z) := by

  have hx: x > 0 ∨ x < 0 := by aesop
  have hy: y > 0 ∨ y < 0 := by aesop
  have hz: z > 0 ∨ z < 0 := by aesop
  -- since x,y,z can only > 0 or < 0, at least two of them have same sign.
  have sign_choose: sign x = sign y ∨ sign y = sign z ∨ sign x = sign z := by
    simp only [← sign_eq_neg_one_iff, ← sign_eq_one_iff] at hx hy hz
    aesop

  -- sign x = sign y = sign z, is to say x,y,z all > 0 or all < 0
  have sign_iff: (sign x = sign y ∧ sign y = sign z) ↔
    (0 < x ∧ 0 < y ∧ 0 < z) ∨ (x < 0 ∧ y < 0 ∧ z < 0) := by
    simp only [← sign_eq_neg_one_iff, ← sign_eq_one_iff] at hx hy hz ⊢
    clear * - hx hy hz
    aesop

  -- if a,b has different sign, then ab < 0
  have mul_neg_sign {a b: ℝ} (ha: a > 0 ∨ a < 0) (hb: b > 0 ∨ b < 0)
    (h: ¬ sign b = sign a):
    a*b < 0 := by
    simp only [← sign_eq_neg_one_iff, ← sign_eq_one_iff] at ha hb
    rw [← sign_eq_neg_one_iff, sign_mul]
    clear * - ha hb h
    aesop


  constructor
  · rintro ⟨h1, h2⟩
    rcases sign_choose with hxy | hyz | hxz
    · -- we may suppose x,y have same sign
      -- if z has same sign, done.
      by_cases hzy: sign z = sign y
      · simp [hxy, hzy]
      -- else, yz < 0, and from first inequality, x(x+y+z) < 0.
      specialize mul_neg_sign hy hz hzy
      replace h1: x * (x+y+z) < 0 := by
        rw [mul_assoc x y z, mul_comm x (y*z), mul_assoc (y*z)] at h1
        exact (neg_iff_neg_of_mul_pos h1).mp mul_neg_sign
      replace h1: x^2 + x*y + x*z < 0 := by linarith only [h1]
      -- add (yz - x^2) to both sides
      replace h1: x*y + y*z + x*z < y*z - x^2 := by
        linarith only [h1]
      -- but cannot be the case yz - x^2 > 0 ,contradiction.
      replace h2 := h2.trans h1
      linarith only [h2, mul_neg_sign, sq_nonneg x]

    · -- basically same as above
      by_cases hxz: sign x = sign z
      · simp [hyz, hxz]
      specialize mul_neg_sign hz hx hxz
      replace h1: y*(x+y+z) < 0 := by
        rw [mul_comm (x*y) z, ← mul_assoc,
        mul_assoc _ y _] at h1
        exact (neg_iff_neg_of_mul_pos h1).mp mul_neg_sign
      linarith only [h1, h2, mul_neg_sign, sq_nonneg y]
    · by_cases hxy: sign y = sign x
      · simp [hxz, hxy]
      specialize mul_neg_sign hx hy hxy
      replace h1: z*(x+y+z) < 0 := by
        rw [mul_assoc _ z _] at h1
        exact (neg_iff_neg_of_mul_pos h1).mp mul_neg_sign
      linarith only [h1, h2, mul_neg_sign, sq_nonneg z]

  · rw [sign_iff]
    rintro (h | h)
    all_goals
      have hxy: 0 < x*y := by
        simp [mul_pos, mul_pos_of_neg_of_neg, h]
      have hyz: 0 < y*z := by
        simp [mul_pos, mul_pos_of_neg_of_neg, h]
      have hxz: 0 < x*z := by
        simp [mul_pos, mul_pos_of_neg_of_neg, h]
      refine ⟨?_, (by linarith only [hxy, hyz, hxz])⟩
    · have hxyz: 0 < x*y*z := by
        apply mul_pos hxy h.right.right
      apply mul_pos hxyz (by linarith only [h])
    · have hxyz: x*y*z < 0 := by
        apply mul_neg_of_pos_of_neg hxy h.right.right
      apply mul_pos_of_neg_of_neg hxyz (by linarith only [h])